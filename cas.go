//go:generate go tool yacc -p Calc -o interp.go interp.y
//go:generate golex -o tokenizer.go tokenizer.l

package cas

import (
	"bytes"
	"github.com/op/go-logging"
	"os"
	"runtime/debug"
	"sort"
	"strings"
)

var format = logging.MustStringFormatter(
	`%{color}%{time:15:04:05.000} %{shortfunc} ▶ %{level:.4s} %{id:03x}%{color:reset} %{message}`,
)

type CASLogger struct {
	_log           *logging.Logger
	leveled        logging.LeveledBackend
	debugState     bool
}

type EvalState struct {
	CASLogger
	defined        map[string][]Expression
	patternDefined map[string]Ex
}

func NewEvalState() *EvalState {
	var es EvalState
	es.defined = make(map[string][]Expression)
	es.patternDefined = make(map[string]Ex)

	// Set up logging
	es.CASLogger._log = logging.MustGetLogger("example")
	backend := logging.NewLogBackend(os.Stderr, "", 0)
	formatter := logging.NewBackendFormatter(backend, format)
	es.CASLogger.leveled = logging.AddModuleLevel(formatter)
	logging.SetBackend(es.CASLogger.leveled)
	es.DebugOff()

	InitCAS(&es)

	return &es
}

func NewEvalStateNoLog() *EvalState {
	var es EvalState
	es.defined = make(map[string][]Expression)
	es.patternDefined = make(map[string]Ex)
	es.CASLogger.debugState = false
	return &es
}

func (this *CASLogger) Debugf(fmt string, args ...interface{}) {
	if this.debugState {
		this._log.Debugf(this.Pre() + fmt, args...)
	}
}

func (this *CASLogger) Infof(fmt string, args ...interface{}) {
	if this.debugState {
		this._log.Infof(this.Pre() + fmt, args...)
	}
}

func (this *CASLogger) DebugOn() {
	this.leveled.SetLevel(logging.DEBUG, "")
	this.debugState = true
}

func (this *CASLogger) DebugOff() {
	this.leveled.SetLevel(logging.ERROR, "")
	this.debugState = false
}

func (this *CASLogger) Pre() string {
	toReturn := ""
	if this.leveled.GetLevel("") != logging.ERROR {
		depth := (bytes.Count(debug.Stack(), []byte{'\n'}) - 15) / 2
		for i := 0; i < depth; i++ {
			toReturn += " "
		}
	}
	return toReturn
}

func (this *EvalState) GetDef(name string, lhs Ex) (Ex, bool) {
	_, isd := this.defined[name]
	if !isd {
		return nil, false
	}
	//this.Debugf("Inside GetDef(\"%s\",%s)", name, lhs)
	this.Debugf("Inside GetDef(\"%s\",%s)", name, lhs)
	oldVars := this.GetDefinedSnapshot()
	for i := range this.defined[name] {
		if IsMatchQ(lhs, this.defined[name][i].Parts[1], this) {
			//Probably not needed:
			//this.ClearPD()
			//this.defined = CopyExpressionMap(oldVars)
			this.Debugf("Found match! Current context before: %s", this)
			res := Replace(lhs, &this.defined[name][i], this)
			this.Debugf("Found match! Current context after: %s", this)
			this.ClearPD()
			this.defined = CopyExpressionMap(oldVars)
			this.Debugf("After reset: %s", this)
			return res, true
		}
		this.ClearPD()
		this.defined = CopyExpressionMap(oldVars)
	}
	return nil, false
}

func (this *EvalState) Define(name string, lhs Ex, rhs Ex) {
	this.Debugf("Inside es.Define(\"%s\",%s,%s)", name, lhs, rhs)
	_, isd := this.defined[name]
	if !isd {
		this.defined[name] = []Expression{{[]Ex{&Symbol{"Rule"}, lhs, rhs}}}
		return
	}

	for i := range this.defined[name] {
		if IsSameQ(this.defined[name][i].Parts[1], lhs, this) {
			this.defined[name][i].Parts[2] = rhs
			return
		}
	}

	// Insert into definitions for name. Maintain order of decreasing
	// complexity. I define complexity as the length of the Lhs.String()
	// because it is simple, and it works for most of the common cases. We wish
	// to attempt f[x_Integer] before we attempt f[x_].
	newLhsLen := len(lhs.String())
	for i := range this.defined[name] {
		thisLhsLen := len(this.defined[name][i].Parts[1].String())
		if thisLhsLen < newLhsLen {
			this.defined[name] = append(this.defined[name][:i], append([]Expression{{[]Ex{&Symbol{"Rule"}, lhs, rhs}}}, this.defined[name][i:]...)...)
			return
		}
	}
	this.defined[name] = append(this.defined[name], Expression{[]Ex{&Symbol{"Rule"}, lhs, rhs}})
}

func (this *EvalState) ClearAll() {
	this.defined = make(map[string][]Expression)
	this.patternDefined = make(map[string]Ex)
	InitCAS(this)
}

func (this *EvalState) Clear(name string) {
	_, ok := this.defined[name]
	if ok {
		delete(this.defined, name)
	}
}

func (this *EvalState) ClearPD() {
	this.patternDefined = make(map[string]Ex)
}

func CopyExpressionMap(in map[string][]Expression) map[string][]Expression {
	out := make(map[string][]Expression)
	for k, v := range in {
		for _, rule := range v {
			out[k] = append(out[k], *rule.DeepCopy().(*Expression))
		}
	}
	return out
}

func (this *EvalState) GetDefinedSnapshot() map[string][]Expression {
	return CopyExpressionMap(this.defined)
}

func (this *EvalState) String() string {
	var buffer bytes.Buffer
	buffer.WriteString("{")
	for k, v := range this.defined {
		buffer.WriteString(k)
		buffer.WriteString(": ")
		buffer.WriteString(ExpressionArrayToString(v))
		buffer.WriteString(", ")
	}
	for k, v := range this.patternDefined {
		buffer.WriteString(k)
		buffer.WriteString("_: ")
		buffer.WriteString(v.String())
		buffer.WriteString(", ")
	}
	if strings.HasSuffix(buffer.String(), ", ") {
		buffer.Truncate(buffer.Len() - 2)
	}
	buffer.WriteString("}")
	return buffer.String()
}

// Ex stands for Expression. Most structs should implement this
type Ex interface {
	Eval(es *EvalState) Ex
	//Replace(r *Expression, es *EvalState) Ex
	String() string
	IsEqual(b Ex, es *EvalState) string
	DeepCopy() Ex
}

// Some utility functions that span multiple files

func ExArrayToString(exArray []Ex) string {
	var buffer bytes.Buffer
	buffer.WriteString("{")
	for i, e := range exArray {
		buffer.WriteString(e.String())
		if i != len(exArray)-1 {
			buffer.WriteString(", ")
		}
	}
	buffer.WriteString("}")
	return buffer.String()
}

func ExpressionArrayToString(exArray []Expression) string {
	var buffer bytes.Buffer
	buffer.WriteString("{")
	for i, e := range exArray {
		buffer.WriteString(e.String())
		if i != len(exArray)-1 {
			buffer.WriteString(", ")
		}
	}
	buffer.WriteString("}")
	return buffer.String()
}

func ExArrayContainsFloat(a []Ex) bool {
	res := false
	for _, e := range a {
		_, isfloat := e.(*Flt)
		res = res || isfloat
	}
	return res
}

func CommutativeIsEqual(components []Ex, other_components []Ex, es *EvalState) string {
	es.Infof("Entering CommutativeIsEqual(components: %s, other_components: %s, es: %s)", ExArrayToString(components), ExArrayToString(other_components), es)
	if len(components) != len(other_components) {
		return "EQUAL_FALSE"
	}
	matched := make(map[int]struct{})
	for _, e1 := range components {
		foundmatch := false
		for j, e2 := range other_components {
			_, taken := matched[j]
			if taken {
				continue
			}
			res := e1.IsEqual(e2, es)
			switch res {
			case "EQUAL_FALSE":
			case "EQUAL_TRUE":
				matched[j] = struct{}{}
				foundmatch = true
			case "EQUAL_UNK":
			}
			if foundmatch {
				break
			}
		}
		if !foundmatch {
			return "EQUAL_UNK"
		}
	}
	return "EQUAL_TRUE"
}

func CommutativeIsMatchQ(components []Ex, lhs_components []Ex, es *EvalState) bool {
	es.Infof("Entering CommutativeIsMatchQ(components: %s, lhs_components: %s, es: %s)", ExArrayToString(components), ExArrayToString(lhs_components), es)
	containsBlankSequence := false
	for i := range lhs_components {
		pat, isPat := HeadAssertion(lhs_components[i], "Pattern")
		_, isBns := HeadAssertion(lhs_components[i], "BlankNullSequence")
		_, isBs := HeadAssertion(lhs_components[i], "BlankSequence")
		if isPat {
			_, isBns = HeadAssertion(pat.Parts[2], "BlankNullSequence")
			_, isBs = HeadAssertion(pat.Parts[2], "BlankSequence")
		}
		if isBs || isBns {
			containsBlankSequence = true
			break
		}
	}
	es.Infof("containsBlankSequence %s", containsBlankSequence)
	// This is because MatchQ[a + b + c, b + c] == False. We should be careful
	// though because MatchQ[a + b + c, c + __] == True.
	if !containsBlankSequence && len(components) != len(lhs_components) {
		es.Debugf("len(components) != len(lhs_components). CommutativeMatchQ failed")
		return false
	}

	// Generate all possible orders of components. There is certainly a more
	// elegant recursive solution, but this is easier for now.
	toPermute := make([]int, len(components))
	for i := range toPermute {
		toPermute[i] = i
	}
	perms := permutations(toPermute, len(components))
	es.Debugf("Permutations to try: %v\n", perms)

	for _, perm := range perms {
		//oldVars := es.GetDefinedSnapshot()
		es.Debugf("Using perm: %v\n", perm)

		// Build a version of components with the correct order. Can I do this
		// more efficiently with a slice notation? Let's copy for now.
		orderedComponents := make([]Ex, len(components))
		for oci, ci := range perm {
			orderedComponents[oci] = components[ci].DeepCopy()
		}
		es.Infof("%s", ExArrayToString(orderedComponents))
		if NonCommutativeIsMatchQ(orderedComponents, lhs_components, es) {
			es.Debugf("CommutativeIsMatchQ succeeded. Context: %s", es)
			return true
		}

		es.ClearPD()
		//es.defined = oldVars
	}
	es.Debugf("CommutativeIsMatchQ failed. Context: %s", es)
	return false
}

func Max(x, y int) int {
	if x > y {
		return x
	}
	return y
}

func Min(x, y int) int {
	if x < y {
		return x
	}
	return y
}

func NonCommutativeIsMatchQ(components []Ex, lhs_components []Ex, es *EvalState) bool {
	// This function is now recursive because of the existence of BlankSequence.
	es.Infof("Entering NonCommutativeIsMatchQ(components: %s, lhs_components: %s, es: %s)", ExArrayToString(components), ExArrayToString(lhs_components), es)
	// A base case for the recursion
	if len(components) == 0 && len(lhs_components) == 0 {
		return true
	}
	if len(components) != 0 && len(lhs_components) == 0 {
		return false
	}

	progressI := 0
	for i := 0; i < Max(len(components), len(lhs_components)); i++ {
		progressI = i
		if i >= len(lhs_components) {
			return false
		}
		if i >= len(components) {
			es.Debugf("Checking if IsMatchQ(INDEX_ERROR, %s). i=%d, Current context: %v\n", lhs_components[i], i, es)
		} else {
			es.Debugf("Checking if IsMatchQ(%s, %s). i=%d, Current context: %v\n", components[i], lhs_components[i], i, es)
		}
		pat, isPat := HeadAssertion(lhs_components[i], "Pattern")
		bns, isBns := HeadAssertion(lhs_components[i], "BlankNullSequence")
		bs, isBs := HeadAssertion(lhs_components[i], "BlankSequence")
		if isPat {
			bns, isBns = HeadAssertion(pat.Parts[2], "BlankNullSequence")
			bs, isBs = HeadAssertion(pat.Parts[2], "BlankSequence")
		}
		if isBns || isBs {
			es.Debugf("Encountered BS or BNS!")
			remainingLhs := make([]Ex, len(lhs_components)-i-1)
			for k := i + 1; k < len(lhs_components); k++ {
				remainingLhs[k-i-1] = lhs_components[k].DeepCopy()
			}
			startI := 0
			if isBns {
				startI = i - 1
			} else {
				startI = i
			}
			for j := startI; j < len(components); j++ {
				// This process involves a lot of extraneous copying. I should
				// test to see how much of these arrays need to be copied from
				// scratch on every iteration.
				seqToTry := make([]Ex, j-i+1)
				for k := i; k <= j; k++ {
					seqToTry[k-i] = components[k].DeepCopy()
				}
				seqMatches := false
				if isBns {
					seqMatches = ExArrayTestRepeatingMatch(seqToTry, BlankNullSequenceToBlank(bns), es)
				} else {
					seqMatches = ExArrayTestRepeatingMatch(seqToTry, BlankSequenceToBlank(bs), es)
				}
				es.Debugf("%v", seqMatches)
				remainingComps := make([]Ex, len(components)-j-1)
				for k := j + 1; k < len(components); k++ {
					remainingComps[k-j-1] = components[k].DeepCopy()
				}
				es.Debugf("%d %s %s %s", j, ExArrayToString(seqToTry), ExArrayToString(remainingComps), ExArrayToString(remainingLhs))
				if seqMatches && NonCommutativeIsMatchQ(remainingComps, remainingLhs, es) {
					if isPat {
						sAsSymbol, sAsSymbolOk := pat.Parts[1].(*Symbol)
						if sAsSymbolOk {
							toTryParts := []Ex{&Symbol{"Sequence"}}
							toTryParts = append(toTryParts, seqToTry...)
							target := &Expression{toTryParts}
							_, isd := es.defined[sAsSymbol.Name]
							_, ispd := es.patternDefined[sAsSymbol.Name]
							if !ispd {
								es.patternDefined[sAsSymbol.Name] = target
							}
							if !IsSameQ(es.patternDefined[sAsSymbol.Name], target, es) {
								return false
							}

							if !isd {
								//es.defined[sAsSymbol.Name] = target
								es.Define(sAsSymbol.Name, sAsSymbol, target)
							} else {
								//return es.defined[sAsSymbol.Name].IsSameQ(target, es)
								return true
							}
						}
					}
					return true
				}
			}
			return false
		}
		if i >= len(components) {
			return false
		}
		if IsMatchQ(components[i].DeepCopy(), lhs_components[i], es) {
			es.Debugf("Returned True!\n")
		} else {
			es.Debugf("NonCommutativeIsMatchQ failed. Context: %s", es)
			return false
		}
	}
	return progressI == len(lhs_components)-1
}

func FunctionIsEqual(components []Ex, other_components []Ex, es *EvalState) string {
	if len(components) != len(other_components) {
		return "EQUAL_UNK"
	}
	for i := range components {
		res := components[i].IsEqual(other_components[i], es)
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

func FunctionIsSameQ(components []Ex, other_components []Ex, es *EvalState) bool {
	if len(components) != len(other_components) {
		return false
	}
	for i := range components {
		res := IsSameQ(components[i], other_components[i], es)
		if !res {
			return false
		}
	}
	return true
}

func IterableReplace(components *[]Ex, r *Expression, es *EvalState) {
	for i := range *components {
		es.Debugf("Attempting IsMatchQ(%s, %s, %s)", (*components)[i], r.Parts[1], es)
		oldVars := es.GetDefinedSnapshot()
		if IsMatchQ((*components)[i], r.Parts[1], es) {
			(*components)[i] = r.Parts[2].DeepCopy()
			es.Debugf("IsMatchQ succeeded, new components: %s", ExArrayToString(*components))
		}
		es.ClearPD()
		es.defined = oldVars
	}
}

func permutations(iterable []int, r int) [][]int {
	res := make([][]int, 0)
	pool := iterable
	n := len(pool)

	if r > n {
		return res
	}

	indices := make([]int, n)
	for i := range indices {
		indices[i] = i
	}

	cycles := make([]int, r)
	for i := range cycles {
		cycles[i] = n - i
	}

	result := make([]int, r)
	for i, el := range indices[:r] {
		result[i] = pool[el]
	}

	c := make([]int, len(result))
	copy(c, result)
	res = append(res, c)

	for n > 0 {
		i := r - 1
		for ; i >= 0; i -= 1 {
			cycles[i] -= 1
			if cycles[i] == 0 {
				index := indices[i]
				for j := i; j < n-1; j += 1 {
					indices[j] = indices[j+1]
				}
				indices[n-1] = index
				cycles[i] = n - i
			} else {
				j := cycles[i]
				indices[i], indices[n-j] = indices[n-j], indices[i]

				for k := i; k < r; k += 1 {
					result[k] = pool[indices[k]]
				}

				c := make([]int, len(result))
				copy(c, result)
				res = append(res, c)

				break
			}
		}

		if i < 0 {
			return res
		}

	}
	return res

}

func CommutativeReplace(components *[]Ex, lhs_components []Ex, rhs Ex, es *EvalState) {
	es.Infof("Entering CommutativeReplace(components: *%s, lhs_components: %s, es: %s)", ExArrayToString(*components), ExArrayToString(lhs_components), es)
	// Each permutation is a potential order of the Rule's LHS in which matches
	// may occur in components.
	toPermute := make([]int, len(*components))
	for i := range toPermute {
		toPermute[i] = i
	}
	perms := permutations(toPermute, len(lhs_components))
	es.Debugf("Permutations to try: %v\n", perms)

	for _, perm := range perms {
		used := make([]int, len(perm))
		pi := 0
		es.Debugf("Before snapshot. Context: %v\n", es)
		oldVars := es.GetDefinedSnapshot()
		for i := range perm {
			//es.Debugf("%s %s\n", (*components)[perm[i]], lhs_components[i])
			if IsMatchQ((*components)[perm[i]].DeepCopy(), lhs_components[i], es) {
				used[pi] = perm[i]
				pi = pi + 1

				if pi == len(perm) {
					sort.Ints(used)
					es.Debugf("About to delete components matching lhs.")
					es.Debugf("components before: %s", ExArrayToString(*components))
					for tdi, todelete := range used {
						*components = append((*components)[:todelete-tdi], (*components)[todelete-tdi+1:]...)
					}
					es.Debugf("components after: %s", ExArrayToString(*components))
					es.Debugf("Appending %s\n", rhs)
					es.Debugf("Context: %v\n", es)
					*components = append(*components, []Ex{rhs.DeepCopy().Eval(es)}...)
					es.Debugf("components after append: %s", ExArrayToString(*components))
					es.ClearPD()
					es.defined = oldVars
					es.Debugf("After clear. Context: %v\n", es)
					return
				}
			}
			es.Debugf("Done checking. Context: %v\n", es)
		}
		es.ClearPD()
		es.defined = oldVars
		es.Debugf("After clear. Context: %v\n", es)
	}
}

func (this *Expression) EvalClear(es *EvalState) Ex {
	for _, arg := range this.Parts[1:] {
		es.Debugf("arg: %v", arg)
		sym, isSym := arg.(*Symbol)
		if isSym {
			es.Clear(sym.Name)
		}
	}
	return &Symbol{"Null"}
}
