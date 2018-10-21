package expreduce

import (
	"fmt"
	"math/big"
	"sort"
	"time"

	"github.com/corywalker/expreduce/expreduce/timecounter"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

func (es *EvalState) Eval(expr expreduceapi.Ex) expreduceapi.Ex {
	if asExpression, ok := expr.(*Expression); ok {
		return es.evalExpression(asExpression)
	}
	if asComplex, ok := expr.(*Complex); ok {
		return es.evalComplex(asComplex)
	}
	if asRational, ok := expr.(*Rational); ok {
		return es.evalRational(asRational)
	}
	if asSymbol, ok := expr.(*Symbol); ok {
		return es.evalSymbol(asSymbol)
	}
	// Other atoms do not need any evaluation logic.
	return expr
}

func (es *EvalState) evalComplex(this *Complex) expreduceapi.Ex {
	this.Re = this.Re.Eval(es)
	this.Im = this.Im.Eval(es)
	if IsSameQ(this.Im, NewInt(0), es.GetLogger()) {
		return this.Re
	}
	this.needsEval = false
	return this
}

func (es *EvalState) Eval(this *Expression) expreduceapi.Ex {
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
			if es.GetTrace() != nil && !es.IsFrozen() {
				toAppend := NewExpression([]expreduceapi.Ex{
					NewSymbol("System`HoldForm"),
					toReturn.DeepCopy(),
				})

				//fmt.Printf("Beginning: appending %v\n", toAppend.StringForm("FullForm"))
				es.GetTrace().AppendEx(toAppend)
			}
			return toReturn
		}

		currStr := ""
		currHeadStr := ""
		started := int64(0)
		if es.IsProfiling() {
			currStr = curr.String(es)
			currHeadStr = curr.GetParts()[0].String(es)
			started = time.Now().UnixNano()
		}

		// Start by evaluating each argument
		headSym, headIsSym := &Symbol{}, false
		attrs := expreduceapi.Attributes{}
		if len(curr.GetParts()) > 0 {
			headSym, headIsSym = curr.GetParts()[0].(*Symbol)
		}
		if headIsSym {
			attrs = headSym.Attrs(es.GetDefinedMap())
		}
		if attrs.NumericFunction {
			propagated, changed := curr.propagateConditionals()
			if changed {
				return propagated.Eval(es)
			}
		}
		for i := range curr.GetParts() {
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
			traceBak := es.GetTrace()
			if es.GetTrace() != nil && !es.IsFrozen() {
				es.SetTrace(NewExpression([]expreduceapi.Ex{NewSymbol("System`List")}))
			}
			oldHash := curr.GetParts()[i].Hash()
			//fmt.Println(curr, i)
			curr.GetParts()[i] = curr.GetParts()[i].Eval(es)
			if es.HasThrown() {
				return es.Thrown()
			}
			if oldHash != curr.GetParts()[i].Hash() {
				curr.cachedHash = 0
			}
			if es.GetTrace() != nil && !es.IsFrozen() {
				if len(es.GetTrace().GetParts()) > 2 {
					// The DeepCopy here doesn't seem to affect anything, but
					// should be good to have.
					//fmt.Printf("Argument eval: appending %v\n", es.trace.DeepCopy().StringForm("FullForm"))
					traceBak.AppendEx(es.GetTrace().DeepCopy())
				}
				es.SetTrace(traceBak)
			}
		}

		// Handle tracing
		if es.GetTrace() != nil && !es.IsFrozen() {
			toAppend := NewExpression([]expreduceapi.Ex{
				NewSymbol("System`HoldForm"),
				currEx.DeepCopy(),
			})

			if !IsSameQ(es.GetTrace().GetParts()[len(es.GetTrace().GetParts())-1], toAppend, es.GetLogger()) {
				//fmt.Printf("Beginning: appending %v\n", toAppend.StringForm("FullForm"))
				es.GetTrace().AppendEx(toAppend)
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

		pureFunction, isPureFunction := HeadAssertion(curr.GetParts()[0], "System`Function")
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

			legacyEvalFn, hasLegacyEvalFn := (expreduceapi.EvalFnType)(nil), false
			if _, inDefined := es.GetDefinedMap().Get(headStr); inDefined {
				if es.GetDefinedMap().GetDef(headStr).LegacyEvalFn != nil {
					hasLegacyEvalFn = true
					legacyEvalFn = es.GetDefinedMap().GetDef(headStr).LegacyEvalFn
				}
			}
			unchanged := true
			if hasLegacyEvalFn {
				currEx = legacyEvalFn(curr, es)
				// TODO: I could potentially have the legacyevalfn return this.
				unchanged = IsSameQ(currEx, curr, es.GetLogger())
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
			currEx = pureFunction.EvalFunction(es, curr.GetParts()[1:])
		}
		currExHash = hashEx(currEx)

		// Handle end of profiling
		if es.IsProfiling() {
			elapsed := float64(time.Now().UnixNano()-started) / 1000000000
			es.GetTimeCounter().AddTime(timecounter.CounterGroupEvalTime, currStr, elapsed)
			es.GetTimeCounter().AddTime(timecounter.CounterGroupHeadEvalTime, currHeadStr, elapsed)
		}
	}
	curr, isExpr := currEx.(*Expression)
	if isExpr {
		curr.needsEval = false
		curr.evaledHash = currExHash
	}
	return currEx
}

func (es *EvalState) evalRational(this *Rational) expreduceapi.Ex {
	if this.Num.Cmp(big.NewInt(0)) == 0 && this.Den.Cmp(big.NewInt(0)) == 0 {
		return NewSymbol("System`Indeterminate")
	}
	if this.Den.Cmp(big.NewInt(0)) == 0 {
		return NewSymbol("System`ComplexInfinity")
	}
	if this.Num.Cmp(big.NewInt(0)) == 0 {
		return NewInteger(big.NewInt(0))
	}
	negNum := this.Num.Cmp(big.NewInt(0)) == -1
	negDen := this.Den.Cmp(big.NewInt(0)) == -1
	negateRes := negNum != negDen
	absNum := big.NewInt(0)
	absNum.Abs(this.Num)
	absDen := big.NewInt(0)
	absDen.Abs(this.Den)

	gcd := big.NewInt(0)
	gcd.GCD(nil, nil, absNum, absDen)
	absNum.Div(absNum, gcd)
	absDen.Div(absDen, gcd)

	if absDen.Cmp(big.NewInt(1)) == 0 {
		if !negateRes {
			return NewInteger(absNum)
		} else {
			return NewInteger(absNum.Neg(absNum))
		}
	}

	if !negateRes {
		this.Num.Set(absNum)
		this.Den.Set(absDen)
		this.needsEval = false
		return this
	}
	this.Num.Set(absNum.Neg(absNum))
	this.Den.Set(absDen)
	this.needsEval = false
	return this
}

func (es *EvalState) evalSymbol(this *Symbol) expreduceapi.Ex {
	//definition, isdefined := es.defined[this.Name]
	definition, isdefined, _ := es.GetDef(this.Name, this)
	if isdefined {
		// We must call Eval because, at this point, the expression has broken
		// out of the evaluation loop.
		toReturn := definition
		// To handle the case where we set a variable to itself.
		if sym, isSym := definition.(*Symbol); isSym {
			if sym.Name == this.Name {
				return toReturn
			}
		}
		toReturn = toReturn.Eval(es)
		retVal, isReturn := tryReturnValue(toReturn, nil, es)
		if isReturn {
			return retVal
		}
		return toReturn
	}
	return this
}

func tryReturnValue(e expreduceapi.Ex, origEx expreduceapi.Ex, es expreduceapi.EvalStateInterface) (expreduceapi.Ex, bool) {
	if es.IsInterrupted() {
		if origEx != nil {
			fmt.Println(origEx)
		}
		return NewSymbol("System`$Aborted"), true
	}
	asReturn, isReturn := HeadAssertion(e, "System`Return")
	if !isReturn {
		return nil, false
	}
	if len(asReturn.GetParts()) >= 2 {
		return asReturn.GetParts()[1], true
	}
	return NewSymbol("System`Null"), true
}

// Is this causing issues by not creating a copy as we modify? Actually it is
// creating copies.
func (this *Expression) mergeSequences(es expreduceapi.EvalStateInterface, headStr string, shouldEval bool) *Expression {
	encounteredSeq := false
	for _, e := range this.GetParts() {
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
	for _, e := range this.GetParts() {
		seq, isseq := HeadAssertion(e, headStr)
		if isseq {
			for _, seqPart := range seq.GetParts()[1:] {
				if shouldEval {
					res.AppendEx(seqPart.Eval(es))
				} else {
					res.AppendEx(seqPart)
				}
			}
		} else {
			res.AppendEx(e)
		}
	}
	return res
}

func (this *Expression) EvalFunction(es expreduceapi.EvalStateInterface, args []expreduceapi.Ex) expreduceapi.Ex {
	if len(this.GetParts()) == 2 {
		toReturn := this.GetParts()[1].DeepCopy()
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
	} else if len(this.GetParts()) == 3 {
		repSym, ok := this.GetParts()[1].(*Symbol)
		if !ok {
			return this
		}
		toReturn := this.GetParts()[2].DeepCopy()
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

func ExprReplaceAll(this expreduceapi.ExpressionInterface, r expreduceapi.ExpressionInterface, stopAtHead string, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
	es.Debugf("In Expression.ReplaceAll. First trying IsMatchQ(this, r.Parts[1], es).")
	es.Debugf("Rule r is: %s", r)

	matchq, matches := IsMatchQ(this, r.GetParts()[1], EmptyPD(), es)
	if matchq {
		es.Debugf("After MatchQ, rule is: %s", r)
		es.Debugf("MatchQ succeeded. Returning r.Parts[2]: %s", r.GetParts()[2])
		return ReplacePD(r.GetParts()[2].DeepCopy(), es, matches)
	}

	thisSym, thisSymOk := this.GetParts()[0].(*Symbol)
	lhsExpr, lhsExprOk := r.GetParts()[1].(*Expression)
	if lhsExprOk {
		otherSym, otherSymOk := lhsExpr.GetParts()[0].(*Symbol)
		if thisSymOk && otherSymOk {
			if thisSym.Name == otherSym.Name {
				attrs := thisSym.Attrs(es.GetDefinedMap())
				if attrs.Flat {
					return FlatReplace(this, lhsExpr, r.GetParts()[2], attrs.Orderless, es)
				}
			}
		}
	}

	maybeChanged := NewEmptyExpression()
	for i := range this.GetParts() {
		maybeChanged.AppendEx(ReplaceAll(this.GetParts()[i], r, es, EmptyPD(), stopAtHead))
	}
	if hashEx(maybeChanged) != hashEx(this) {
		return maybeChanged
	}
	return this
}
