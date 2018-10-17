package expreduce

import (
	"bytes"
	"encoding/binary"
	"flag"
	"fmt"
	"hash/fnv"
	"math/big"
	"sort"
	"sync/atomic"
	"time"

	"github.com/corywalker/expreduce/expreduce/logging"
	"github.com/corywalker/expreduce/expreduce/timecounter"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

var printevals = flag.Bool("printevals", false, "")
var checkhashes = flag.Bool("checkhashes", false, "")

type Expression struct {
	Parts                 []expreduceapi.Ex
	needsEval             bool
	correctlyInstantiated bool
	evaledHash            uint64
	cachedHash            uint64
}

// Deprecated in favor of headExAssertion
func HeadAssertion(ex expreduceapi.Ex, head string) (*Expression, bool) {
	expr, isExpr := ex.(*Expression)
	if isExpr {
		sym, isSym := expr.Parts[0].(*Symbol)
		if isSym {
			if sym.Name == head {
				return expr, true
			}
		}
	}
	return nil, false
}

func headExAssertion(ex expreduceapi.Ex, head expreduceapi.Ex, cl *logging.CASLogger) (*Expression, bool) {
	expr, isExpr := ex.(*Expression)
	if isExpr {
		if IsSameQ(head, expr.Parts[0], cl) {
			return expr, true
		}
	}
	return nil, false
}

func OperatorAssertion(ex expreduceapi.Ex, opHead string) (*Expression, *Expression, bool) {
	expr, isExpr := ex.(*Expression)
	if isExpr {
		headExpr, headIsExpr := expr.Parts[0].(*Expression)
		if headIsExpr {
			sym, isSym := headExpr.Parts[0].(*Symbol)
			if isSym {
				if sym.Name == opHead {
					return expr, headExpr, true
				}
			}
		}
	}
	return nil, nil, false
}

func tryReturnValue(e expreduceapi.Ex, origEx expreduceapi.Ex, es expreduceapi.EvalStateInterface) (expreduceapi.Ex, bool) {
	if es.interrupted {
		if origEx != nil {
			fmt.Println(origEx)
		}
		return NewSymbol("System`$Aborted"), true
	}
	asReturn, isReturn := HeadAssertion(e, "System`Return")
	if !isReturn {
		return nil, false
	}
	if len(asReturn.Parts) >= 2 {
		return asReturn.Parts[1], true
	}
	return NewSymbol("System`Null"), true
}

// Is this causing issues by not creating a copy as we modify? Actually it is
// creating copies.
func (this *Expression) mergeSequences(es *expreduceapi.EvalStateInterface, headStr string, shouldEval bool) *Expression {
	encounteredSeq := false
	for _, e := range this.Parts {
		if _, isseq := HeadAssertion(e, headStr); isseq {
			encounteredSeq = true
			break
		}
	}
	// Only build a new expression if the expression actually has a sequence
	// needing merging.
	if !encounteredSeq {
		return this
	}

	// TODO: I should not be attempting to merge the head if it happens to be
	// a Sequence type. This is very similar to the flatten function. Perhaps
	// it should be combined. This version is not recursive, and it does not
	// accept level depths. It is a specific case of Flatten.
	res := NewEmptyExpression()
	for _, e := range this.Parts {
		seq, isseq := HeadAssertion(e, headStr)
		if isseq {
			for _, seqPart := range seq.Parts[1:] {
				if shouldEval {
					res.Parts = append(res.Parts, seqPart.Eval(es))
				} else {
					res.Parts = append(res.Parts, seqPart)
				}
			}
		} else {
			res.Parts = append(res.Parts, e)
		}
	}
	return res
}

func (this *Expression) propagateConditionals() (*Expression, bool) {
	foundCond := false
	for _, e := range this.Parts[1:] {
		if cond, isCond := HeadAssertion(e, "System`ConditionalExpression"); isCond {
			if len(cond.Parts) == 3 {
				foundCond = true
				break
			}
		}
	}
	if foundCond {
		resEx := E(this.Parts[0])
		resCond := E(S("And"))
		for _, e := range this.Parts[1:] {
			if cond, isCond := HeadAssertion(e, "System`ConditionalExpression"); isCond {
				if len(cond.Parts) == 3 {
					resEx.appendEx(cond.Parts[1].DeepCopy())
					resCond.appendEx(cond.Parts[2].DeepCopy())
					continue
				}
			}
			resEx.appendEx(e.DeepCopy())
		}
		return E(S("ConditionalExpression"), resEx, resCond), true
	}
	return this, false
}

func (this *Expression) Eval(es expreduceapi.EvalStateInterface) expreduceapi.Ex {
	var origEx expreduceapi.Ex = this

	lastExHash := uint64(0)
	var lastEx expreduceapi.Ex = this
	currExHash := hashEx(this)
	if currExHash == this.evaledHash {
		return this
	}
	var currEx expreduceapi.Ex = this
	insideDefinition := false
	for currExHash != lastExHash {
		lastExHash = currExHash
		curr, isExpr := currEx.(*Expression)
		if *checkhashes {
			if isExpr && curr.evaledHash != 0 && currExHash != curr.evaledHash {
				fmt.Printf("invalid cache: %v. Used to be %v\n", curr, lastEx)
			}
			lastEx = currEx
		}

		if isExpr && insideDefinition {
			retVal, isReturn := tryReturnValue(curr, origEx, es)
			if isReturn {
				return retVal
			}
		}
		if isExpr && currExHash == curr.evaledHash {
			return curr
		}

		if *printevals {
			fmt.Printf("Evaluating %v.\n", currEx)
		}
		// Transition to the right Eval() if this is no longer an Expression
		if !isExpr {
			toReturn := currEx.Eval(es)
			// Handle tracing
			if es.trace != nil && !es.IsFrozen() {
				toAppend := NewExpression([]expreduceapi.Ex{
					NewSymbol("System`HoldForm"),
					toReturn.DeepCopy(),
				})

				//fmt.Printf("Beginning: appending %v\n", toAppend.StringForm("FullForm"))
				es.trace.Parts = append(
					es.trace.Parts,
					toAppend,
				)
			}
			return toReturn
		}

		currStr := ""
		currHeadStr := ""
		started := int64(0)
		if es.IsProfiling() {
			currStr = curr.String(es)
			currHeadStr = curr.Parts[0].String(es)
			started = time.Now().UnixNano()
		}

		// Start by evaluating each argument
		headSym, headIsSym := &Symbol{}, false
		attrs := Attributes{}
		if len(curr.Parts) > 0 {
			headSym, headIsSym = curr.Parts[0].(*Symbol)
		}
		if headIsSym {
			attrs = headSym.Attrs(&es.defined)
		}
		if attrs.NumericFunction {
			propagated, changed := curr.propagateConditionals()
			if changed {
				return propagated.Eval(es)
			}
		}
		for i := range curr.Parts {
			if headIsSym && i == 1 && attrs.HoldFirst {
				continue
			}
			if headIsSym && i > 1 && attrs.HoldRest {
				continue
			}
			if headIsSym && (attrs.HoldAll || attrs.HoldAllComplete) {
				continue
			}

			// Handle tracing
			traceBak := es.trace
			if es.trace != nil && !es.IsFrozen() {
				es.trace = NewExpression([]expreduceapi.Ex{NewSymbol("System`List")})
			}
			oldHash := curr.Parts[i].Hash()
			//fmt.Println(curr, i)
			curr.Parts[i] = curr.Parts[i].Eval(es)
			if es.HasThrown() {
				return es.thrown
			}
			if oldHash != curr.Parts[i].Hash() {
				curr.cachedHash = 0
			}
			if es.trace != nil && !es.IsFrozen() {
				if len(es.trace.Parts) > 2 {
					// The DeepCopy here doesn't seem to affect anything, but
					// should be good to have.
					//fmt.Printf("Argument eval: appending %v\n", es.trace.DeepCopy().StringForm("FullForm"))
					traceBak.Parts = append(traceBak.Parts, es.trace.DeepCopy())
				}
				es.trace = traceBak
			}
		}

		// Handle tracing
		if es.trace != nil && !es.IsFrozen() {
			toAppend := NewExpression([]expreduceapi.Ex{
				NewSymbol("System`HoldForm"),
				currEx.DeepCopy(),
			})

			if !IsSameQ(es.trace.Parts[len(es.trace.Parts)-1], toAppend, &es.CASLogger) {
				//fmt.Printf("Beginning: appending %v\n", toAppend.StringForm("FullForm"))
				es.trace.Parts = append(
					es.trace.Parts,
					toAppend,
				)
			}
		}

		// If any of the parts are Sequence, merge them with parts
		if headIsSym {
			if !attrs.SequenceHold && !attrs.HoldAllComplete {
				curr = curr.mergeSequences(es, "System`Sequence", false)
			}
		} else {
			curr = curr.mergeSequences(es, "System`Sequence", false)
		}
		if !attrs.HoldAllComplete {
			curr = curr.mergeSequences(es, "System`Evaluate", true)
		}
		curr = curr.mergeSequences(es, "System`Unevaluated", false)
		// In case curr changed
		currEx = curr

		pureFunction, isPureFunction := HeadAssertion(curr.Parts[0], "System`Function")
		if headIsSym {
			if attrs.Flat {
				curr = curr.mergeSequences(es, headSym.Name, false)
			}
			if attrs.Orderless {
				sort.Sort(curr)
				curr.cachedHash = 0
			}
			if attrs.Listable {
				changed := false
				currEx, changed = ThreadExpr(curr)
				if changed {
					currExHash = hashEx(currEx)
					continue
				}
			}
			headStr := headSym.Name

			legacyEvalFn, hasLegacyEvalFn := (func(*Expression, *expreduceapi.EvalStateInterface) expreduceapi.Ex)(nil), false
			if _, inDefined := es.defined.Get(headStr); inDefined {
				if es.defined.GetDef(headStr).legacyEvalFn != nil {
					hasLegacyEvalFn = true
					legacyEvalFn = es.defined.GetDef(headStr).legacyEvalFn
				}
			}
			unchanged := true
			if hasLegacyEvalFn {
				currEx = legacyEvalFn(curr, es)
				// TODO: I could potentially have the legacyevalfn return this.
				unchanged = IsSameQ(currEx, curr, &es.CASLogger)
			}
			if unchanged {
				theRes, isDefined, def := es.GetDef(headStr, curr)
				if isDefined {
					//fmt.Printf("%v, %v, %v\n", headStr, curr, theRes)
					es.Infof("Def: %v ▶ %v ▶ using %v ▶ from %s head", currEx, theRes, def, headStr)
					currEx = theRes
					insideDefinition = true
				}
			}
		} else if isPureFunction {
			currEx = pureFunction.EvalFunction(es, curr.Parts[1:])
		}
		currExHash = hashEx(currEx)

		// Handle end of profiling
		if es.IsProfiling() {
			elapsed := float64(time.Now().UnixNano()-started) / 1000000000
			es.timeCounter.AddTime(timecounter.CounterGroupEvalTime, currStr, elapsed)
			es.timeCounter.AddTime(timecounter.CounterGroupHeadEvalTime, currHeadStr, elapsed)
		}
	}
	curr, isExpr := currEx.(*Expression)
	if isExpr {
		curr.needsEval = false
		curr.evaledHash = currExHash
	}
	return currEx
}

func (this *Expression) EvalFunction(es *expreduceapi.EvalStateInterface, args []expreduceapi.Ex) expreduceapi.Ex {
	if len(this.Parts) == 2 {
		toReturn := this.Parts[1].DeepCopy()
		for i, arg := range args {
			toReturn = ReplaceAll(toReturn,
				NewExpression([]expreduceapi.Ex{
					NewSymbol("System`Rule"),
					NewExpression([]expreduceapi.Ex{
						NewSymbol("System`Slot"),
						NewInteger(big.NewInt(int64(i + 1))),
					}),

					arg,
				}),

				es, EmptyPD(), "System`Function")
		}
		return toReturn
	} else if len(this.Parts) == 3 {
		repSym, ok := this.Parts[1].(*Symbol)
		if !ok {
			return this
		}
		toReturn := this.Parts[2].DeepCopy()
		toReturn = ReplaceAll(toReturn,
			NewExpression([]expreduceapi.Ex{
				NewSymbol("System`Rule"),
				repSym,
				args[0],
			}),

			es, EmptyPD(), "System`Function")
		return toReturn
	}
	return this
}

func (this *Expression) ReplaceAll(r *Expression, stopAtHead string, es *expreduceapi.EvalStateInterface) expreduceapi.Ex {
	es.Debugf("In Expression.ReplaceAll. First trying IsMatchQ(this, r.Parts[1], es).")
	es.Debugf("Rule r is: %s", r)

	matchq, matches := IsMatchQ(this, r.Parts[1], EmptyPD(), es)
	if matchq {
		es.Debugf("After MatchQ, rule is: %s", r)
		es.Debugf("MatchQ succeeded. Returning r.Parts[2]: %s", r.Parts[2])
		return ReplacePD(r.Parts[2].DeepCopy(), es, matches)
	}

	thisSym, thisSymOk := this.Parts[0].(*Symbol)
	lhsExpr, lhsExprOk := r.Parts[1].(*Expression)
	if lhsExprOk {
		otherSym, otherSymOk := lhsExpr.Parts[0].(*Symbol)
		if thisSymOk && otherSymOk {
			if thisSym.Name == otherSym.Name {
				attrs := thisSym.Attrs(&es.defined)
				if attrs.Flat {
					return FlatReplace(this, lhsExpr, r.Parts[2], attrs.Orderless, es)
				}
			}
		}
	}

	maybeChanged := NewEmptyExpression()
	for i := range this.Parts {
		maybeChanged.Parts = append(maybeChanged.Parts, ReplaceAll(this.Parts[i], r, es, EmptyPD(), stopAtHead))
	}
	if hashEx(maybeChanged) != hashEx(this) {
		return maybeChanged
	}
	return this
}

func (this *Expression) StringForm(params expreduceapi.ToStringParams) string {
	headAsSym, isHeadSym := this.Parts[0].(*Symbol)
	fullForm := false
	if isHeadSym && !fullForm {
		res, ok := "", false
		headStr := headAsSym.Name
		toStringFn, hasToStringFn := params.esi.GetStringFn(headStr)
		if hasToStringFn {
			ok, res = toStringFn(this, params)
		}
		if ok {
			return res
		}
	}

	if len(this.Parts) == 2 && isHeadSym && (headAsSym.Name == "System`InputForm" ||
		headAsSym.Name == "System`FullForm" ||
		headAsSym.Name == "System`TraditionalForm" ||
		headAsSym.Name == "System`TeXForm" ||
		headAsSym.Name == "System`StandardForm" ||
		headAsSym.Name == "System`OutputForm") {
		mutatedParams := params
		mutatedParams.form = headAsSym.Name[7:]
		return this.Parts[1].StringForm(mutatedParams)
	}

	// Default printing format
	var buffer bytes.Buffer
	buffer.WriteString(this.Parts[0].StringForm(params))
	buffer.WriteString("[")
	params.previousHead = "<TOPLEVEL>"
	for i, e := range this.Parts {
		if i == 0 {
			continue
		}
		buffer.WriteString(e.StringForm(params))
		if i != len(this.Parts)-1 {
			buffer.WriteString(", ")
		}
	}
	buffer.WriteString("]")
	return buffer.String()
}

func (this *Expression) String(esi expreduceapi.EvalStateInterface) string {
	context, contextPath := DefaultStringFormArgs()
	return this.StringForm(expreduceapi.ToStringParams{
		form: "InputForm", context: context, contextPath: contextPath, esi: esi})
}

func (this *Expression) IsEqual(otherEx expreduceapi.Ex) string {
	other, ok := otherEx.(*Expression)
	if !ok {
		return "EQUAL_UNK"
	}

	if len(this.Parts) != len(other.Parts) {
		return "EQUAL_UNK"
	}
	for i := range this.Parts {
		res := this.Parts[i].IsEqual(other.Parts[i])
		switch res {
		case "EQUAL_FALSE":
			return "EQUAL_UNK"
		case "EQUAL_TRUE":
		case "EQUAL_UNK":
			return "EQUAL_UNK"
		}
	}
	return "EQUAL_TRUE"
}

func (this *Expression) DeepCopy() expreduceapi.Ex {
	var thiscopy = NewEmptyExpression()
	for i := range this.Parts {
		thiscopy.Parts = append(thiscopy.Parts, this.Parts[i].DeepCopy())
	}
	thiscopy.needsEval = this.needsEval
	thiscopy.correctlyInstantiated = this.correctlyInstantiated
	thiscopy.evaledHash = this.evaledHash
	thiscopy.cachedHash = this.cachedHash
	return thiscopy
}

func (this *Expression) ShallowCopy() *Expression {
	var thiscopy = NewEmptyExpression()
	thiscopy.Parts = append([]expreduceapi.Ex{}, this.Parts...)
	thiscopy.needsEval = this.needsEval
	thiscopy.correctlyInstantiated = this.correctlyInstantiated
	thiscopy.evaledHash = this.evaledHash
	thiscopy.cachedHash = this.cachedHash
	return thiscopy
}

func (this *Expression) Copy() expreduceapi.Ex {
	var thiscopy = NewEmptyExpressionOfLength(len(this.Parts))
	for i := range this.Parts {
		thiscopy.Parts[i] = this.Parts[i].Copy()
	}
	thiscopy.needsEval = this.needsEval
	thiscopy.correctlyInstantiated = this.correctlyInstantiated
	thiscopy.evaledHash = this.evaledHash
	thiscopy.cachedHash = this.cachedHash
	return thiscopy
}

// Implement the sort.Interface
func (this *Expression) Len() int {
	return len(this.Parts) - 1
}

func (this *Expression) Less(i, j int) bool {
	return ExOrder(this.Parts[i+1], this.Parts[j+1]) == 1
}

func (this *Expression) Swap(i, j int) {
	this.Parts[j+1], this.Parts[i+1] = this.Parts[i+1], this.Parts[j+1]
}

func (this *Expression) appendEx(e expreduceapi.Ex) {
	this.Parts = append(this.Parts, e)
}

func (this *Expression) appendExArray(e []expreduceapi.Ex) {
	this.Parts = append(this.Parts, e...)
}

func (this *Expression) NeedsEval() bool {
	return this.needsEval
}

func (this *Expression) Hash() uint64 {
	if atomic.LoadUint64(&this.cachedHash) > 0 {
		return this.cachedHash
	}
	h := fnv.New64a()
	h.Write([]byte{72, 5, 244, 86, 5, 210, 69, 30})
	b := make([]byte, 8)
	for _, part := range this.Parts {
		binary.LittleEndian.PutUint64(b, part.Hash())
		h.Write(b)
	}
	atomic.StoreUint64(&this.cachedHash, h.Sum64())
	return h.Sum64()
}

func (this *Expression) HeadStr() string {
	sym, isSym := this.Parts[0].(*Symbol)
	if isSym {
		return sym.Name
	}
	return ""
}

func NewExpression(parts []expreduceapi.Ex) *Expression {
	return &expreduceapi.ExpressionInterface{
		Parts:                 parts,
		needsEval:             true,
		correctlyInstantiated: true,
	}
}

func E(parts ...expreduceapi.Ex) *Expression {
	return NewExpression(parts)
}

func NewHead(head string) *Expression {
	return NewExpression([]expreduceapi.Ex{NewSymbol(head)})
}

func NewEmptyExpression() *Expression {
	return &expreduceapi.ExpressionInterface{
		needsEval:             true,
		correctlyInstantiated: true,
	}
}

func NewEmptyExpressionOfLength(n int) *Expression {
	return &expreduceapi.ExpressionInterface{
		Parts:                 make([]expreduceapi.Ex, n),
		needsEval:             true,
		correctlyInstantiated: true,
	}
}

func (this *Expression) GetParts() []expreduceapi.Ex {
	return this.Parts
}
