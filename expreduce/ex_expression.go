package expreduce

import "bytes"
import "math/big"
import "sort"

type Expression struct {
	Parts []Ex
}

// Deprecated in favor of headExAssertion
func HeadAssertion(ex Ex, head string) (*Expression, bool) {
	expr, isExpr := ex.(*Expression)
	if isExpr {
		sym, isSym := expr.Parts[0].(*Symbol)
		if isSym {
			if sym.Name == head {
				return expr, true
			}
		}
	}
	return &Expression{}, false
}

func headExAssertion(ex Ex, head Ex, cl *CASLogger) (*Expression, bool) {
	expr, isExpr := ex.(*Expression)
	if isExpr {
		if IsSameQ(head, expr.Parts[0], cl) {
			return expr, true
		}
	}
	return &Expression{}, false
}

// Is this causing issues by not creating a copy as we modify? Actually it is
// creating copies.
func (this *Expression) mergeSequences(es *EvalState, headStr string, shouldEval bool) {
	// TODO: I should not be attempting to merge the head if it happens to be
	// a Sequence type. This is very similar to the flatten function. Perhaps
	// it should be combined. This version is not recursive, and it does not
	// accept level depths. It is a specific case of Flatten.
	origLen := len(this.Parts)
	offset := 0
	for i := 0; i < origLen; i++ {
		j := i + offset
		e := this.Parts[j]
		seq, isseq := HeadAssertion(e, headStr)
		if shouldEval {
			for j := 1; j < len(seq.Parts); j++ {
				seq.Parts[j] = seq.Parts[j].Eval(es)
			}
		}
		if isseq {
			start := j
			end := j + 1
			if j == 0 {
				this.Parts = append(seq.Parts[1:], this.Parts[end:]...)
			} else if j == len(this.Parts)-1 {
				this.Parts = append(this.Parts[:start], seq.Parts[1:]...)
			} else {
				// All of these deep copies may not be needed.
				this.Parts = append(append(this.DeepCopy().(*Expression).Parts[:start], seq.DeepCopy().(*Expression).Parts[1:]...), this.DeepCopy().(*Expression).Parts[end:]...)
			}
			offset += len(seq.Parts[1:]) - 1
		}
	}
}

func (this *Expression) Eval(es *EvalState) Ex {
	shouldEval := true
	var lastEx Ex = this.DeepCopy()
	var currEx Ex = this.DeepCopy()
	for shouldEval {
		curr, isExpr := currEx.(*Expression)
		// Transition to the right Eval() if this is no longer an Expression
		if !isExpr {
			toReturn := currEx.Eval(es)
			// Handle tracing
			if es.trace != nil {
				toAppend := &Expression{[]Ex{
					&Symbol{"HoldForm"},
					toReturn.DeepCopy(),
				}}
				//fmt.Printf("Beginning: appending %v\n", toAppend.StringForm("FullForm"))
				es.trace.Parts = append(
					es.trace.Parts,
					toAppend,
				)
			}
			return toReturn
		}

		// Start by evaluating each argument
		headSym, headIsSym := &Symbol{}, false
		attrs := Attributes{}
		if len(curr.Parts) > 0 {
			headSym, headIsSym = curr.Parts[0].(*Symbol)
		}
		if headIsSym {
			attrs = headSym.Attrs(es)
		}
		for i := range curr.Parts {
			if headIsSym && i == 1 && attrs.HoldFirst {
				continue
			}
			if headIsSym && i > 1 && attrs.HoldRest {
				continue
			}
			if headIsSym && attrs.HoldAll {
				continue
			}

			// Handle tracing
			traceBak := es.trace
			if es.trace != nil {
				es.trace = &Expression{[]Ex{&Symbol{"List"}}}
			}
			curr.Parts[i] = curr.Parts[i].Eval(es)
			if es.trace != nil {
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
		if es.trace != nil {
			toAppend := &Expression{[]Ex{
				&Symbol{"HoldForm"},
				currEx.DeepCopy(),
			}}
			if !IsSameQ(es.trace.Parts[len(es.trace.Parts)-1], toAppend, &es.CASLogger) {
				//fmt.Printf("Beginning: appending %v\n", toAppend.StringForm("FullForm"))
				es.trace.Parts = append(
					es.trace.Parts,
					toAppend,
				)
			}
		}

		// If any of the parts are Sequence, merge them with parts
		curr.mergeSequences(es, "Sequence", false)
		curr.mergeSequences(es, "Evaluate", true)

		pureFunction, isPureFunction := HeadAssertion(curr.Parts[0], "Function")
		if headIsSym {
			if attrs.Flat {
				curr.mergeSequences(es, headSym.Name, false)
			}
			if attrs.Orderless {
				sort.Sort(curr)
			}
			headStr := headSym.Name

			theRes, isDefined := es.GetDef(headStr, curr)
			legacyEvalFn, hasLegacyEvalFn := (func(*Expression, *EvalState) Ex)(nil), false
			if _, inDefined := es.defined[headStr]; inDefined {
				if es.defined[headStr].legacyEvalFn != nil {
					hasLegacyEvalFn = true
					legacyEvalFn = es.defined[headStr].legacyEvalFn
				}
			}
			if isDefined {
				//fmt.Printf("%v, %v, %v\n", headStr, curr, theRes)
				currEx = theRes
			} else if hasLegacyEvalFn {
				currEx = legacyEvalFn(curr, es)
			}
		} else if isPureFunction {
			currEx = pureFunction.EvalFunction(es, curr.Parts[1:])
		}
		if IsSameQ(currEx, lastEx, &es.CASLogger) {
			shouldEval = false
		} else {
			// Handle tracing
			/*
				if es.trace != nil {
					toAppend := &Expression{[]Ex{
						&Symbol{"HoldForm"},
						currEx.DeepCopy(),
					}}
					fmt.Printf("Change: appending %v\n", toAppend.StringForm("FullForm"))
					es.trace.Parts = append(
						es.trace.Parts,
						toAppend,
					)
				}*/
		}
		lastEx = currEx
	}
	return currEx
}

func (this *Expression) EvalFunction(es *EvalState, args []Ex) Ex {
	if len(this.Parts) == 2 {
		toReturn := this.Parts[1].DeepCopy()
		for i, arg := range args {
			toReturn = ReplaceAll(toReturn,
				&Expression{[]Ex{
					&Symbol{"Rule"},
					&Expression{[]Ex{
						&Symbol{"Slot"},
						&Integer{big.NewInt(int64(i + 1))},
					}},
					arg,
				}}, &es.CASLogger, EmptyPD())
		}
		return toReturn
	} else if len(this.Parts) == 3 {
		repSym, ok := this.Parts[1].(*Symbol)
		if !ok {
			return this
		}
		toReturn := this.Parts[2].DeepCopy()
		toReturn = ReplaceAll(toReturn,
			&Expression{[]Ex{
				&Symbol{"Rule"},
				repSym,
				args[0],
			}}, &es.CASLogger, EmptyPD())
		return toReturn
	}
	return this
}

func (this *Expression) ReplaceAll(r *Expression, cl *CASLogger) Ex {
	cl.Debugf("In Expression.ReplaceAll. First trying IsMatchQ(this, r.Parts[1], es).")
	cl.Debugf("Rule r is: %s", r)

	matchq, matches := IsMatchQ(this, r.Parts[1], EmptyPD(), cl)
	toreturn := ReplacePD(r.Parts[2].DeepCopy(), cl, matches)
	if matchq {
		cl.Debugf("After MatchQ, rule is: %s", r)
		cl.Debugf("MatchQ succeeded. Returning r.Parts[2]: %s", r.Parts[2])
		return toreturn
	}

	thisSym, thisSymOk := this.Parts[0].(*Symbol)
	lhsExpr, lhsExprOk := r.Parts[1].(*Expression)
	if lhsExprOk {
		otherSym, otherSymOk := lhsExpr.Parts[0].(*Symbol)
		if thisSymOk && otherSymOk {
			if thisSym.Name == otherSym.Name {
				if IsOrderless(thisSym) {
					cl.Debugf("r.Parts[1] is Orderless. Now running OrderlessReplace")
					replaced := this.Parts[1:len(this.Parts)]
					OrderlessReplace(&replaced, lhsExpr.Parts[1:len(lhsExpr.Parts)], r.Parts[2], cl)
					this.Parts = this.Parts[0:1]
					this.Parts = append(this.Parts, replaced...)
				}
			}
		}
	}

	for i := range this.Parts {
		this.Parts[i] = ReplaceAll(this.Parts[i], r, cl, EmptyPD())
	}
	return this
}

func (this *Expression) StringForm(form string) string {
	headAsSym, isHeadSym := this.Parts[0].(*Symbol)
	fullForm := false
	if isHeadSym && !fullForm {
		res, ok := "", false
		headStr := headAsSym.Name
		toStringFn, hasToStringFn := toStringFns[headStr]
		if hasToStringFn {
			ok, res = toStringFn(this, form)
		}
		if ok {
			return res
		}
	}

	// Default printing format
	var buffer bytes.Buffer
	buffer.WriteString(this.Parts[0].String())
	buffer.WriteString("[")
	for i, e := range this.Parts {
		if i == 0 {
			continue
		}
		buffer.WriteString(e.StringForm(form))
		if i != len(this.Parts)-1 {
			buffer.WriteString(", ")
		}
	}
	buffer.WriteString("]")
	return buffer.String()
}

func (this *Expression) String() string {
	return this.StringForm("InputForm")
}

// TODO: convert to a map
func IsOrderless(sym *Symbol) bool {
	if sym.Name == "Times" {
		return true
	} else if sym.Name == "Plus" {
		return true
	} else if sym.Name == "orderlessFoo" {
		return true
	}
	return false
}

func (this *Expression) IsEqual(otherEx Ex, cl *CASLogger) string {
	other, ok := otherEx.(*Expression)
	if !ok {
		return "EQUAL_UNK"
	}

	if len(this.Parts) != len(other.Parts) {
		return "EQUAL_UNK"
	}
	for i := range this.Parts {
		res := this.Parts[i].IsEqual(other.Parts[i], cl)
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

func (this *Expression) DeepCopy() Ex {
	var thiscopy = &Expression{}
	for i := range this.Parts {
		thiscopy.Parts = append(thiscopy.Parts, this.Parts[i].DeepCopy())
	}
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

func (this *Expression) appendEx(e Ex) {
	this.Parts = append(this.Parts, e)
}
