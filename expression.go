package cas

import "bytes"
import "fmt"
import "math/big"

type Expression struct {
	Parts []Ex
}

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

func (this *Expression) mergeSequences(es *EvalState, headStr string, shouldEval bool) {
	// TODO: I should not be attempting to merge the head if it happens to be
	// a Sequence type
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
			return currEx.Eval(es)
		}

		// Start by evaluating each argument
		headSym, headIsSym := &Symbol{}, false
		if len(curr.Parts) > 0 {
			headSym, headIsSym = curr.Parts[0].(*Symbol)
		}
		for i := range curr.Parts {
			if headIsSym && i == 1 && IsHoldFirst(headSym) {
				continue
			}
			if headIsSym && i > 1 && IsHoldRest(headSym) {
				continue
			}
			//if headIsSym && IsAttribute(headSym, "HoldAll", es) {
			if headIsSym && IsHoldAll(headSym) {
				continue
			}
			curr.Parts[i] = curr.Parts[i].Eval(es)
		}

		// If any of the parts are Sequence, merge them with parts
		curr.mergeSequences(es, "Sequence", false)
		curr.mergeSequences(es, "Evaluate", true)

		headAsSym, isHeadSym := curr.Parts[0].(*Symbol)
		pureFunction, isPureFunction := HeadAssertion(curr.Parts[0], "Function")
		if isHeadSym {
			headStr := headAsSym.Name

			theRes, isDefined := es.GetDef(headStr, curr)
			if isDefined {
				currEx = theRes
			} else if headStr == "Power" {
				currEx = curr.EvalPower(es)
			} else if headStr == "Equal" {
				currEx = curr.EvalEqual(es)
			} else if headStr == "SameQ" {
				currEx = curr.EvalSameQ(es)
			} else if headStr == "Plus" {
				currEx = curr.EvalPlus(es)
			} else if headStr == "Times" {
				currEx = curr.EvalTimes(es)
			} else if headStr == "Set" {
				currEx = curr.EvalSet(es)
			} else if headStr == "SetDelayed" {
				currEx = curr.EvalSetDelayed(es)
			} else if headStr == "If" {
				currEx = curr.EvalIf(es)
			} else if headStr == "While" {
				currEx = curr.EvalWhile(es)
			} else if headStr == "MatchQ" {
				currEx = curr.EvalMatchQ(es)
			} else if headStr == "ReplaceAll" {
				currEx = curr.EvalReplaceAll(es)
			} else if headStr == "ReplaceRepeated" {
				currEx = curr.EvalReplaceRepeated(es)
			} else if headStr == "SetLogging" {
				currEx = curr.EvalSetLogging(es)
			} else if headStr == "Definition" {
				currEx = curr.EvalDefinition(es)
			} else if headStr == "Order" {
				currEx = curr.EvalOrder(es)
			} else if headStr == "Sort" {
				currEx = curr.EvalSort(es)
			} else if headStr == "RandomReal" {
				currEx = curr.EvalRandomReal(es)
			} else if headStr == "SeedRandom" {
				currEx = curr.EvalSeedRandom(es)
			} else if headStr == "UnixTime" {
				currEx = curr.EvalUnixTime(es)
			} else if headStr == "Apply" {
				currEx = curr.EvalApply(es)
			} else if headStr == "Length" {
				currEx = curr.EvalLength(es)
			} else if headStr == "Table" {
				currEx = curr.EvalTable(es)
			} else if headStr == "Sum" {
				currEx = curr.EvalSum(es)
			} else if headStr == "Product" {
				currEx = curr.EvalProduct(es)
			} else if headStr == "Clear" {
				currEx = curr.EvalClear(es)
			} else if headStr == "Timing" {
				currEx = curr.EvalTiming(es)
			} else if headStr == "MemberQ" {
				currEx = curr.EvalMemberQ(es)
			} else if headStr == "Print" {
				currEx = curr.EvalPrint(es)
			} else if headStr == "CompoundExpression" {
				currEx = curr.EvalCompoundExpression(es)
			} else if headStr == "Map" {
				currEx = curr.EvalMap(es)
			} else if headStr == "Factorial" {
				currEx = curr.EvalFactorial(es)
			} else if headStr == "Head" {
				currEx = curr.EvalHead(es)
			} else if headStr == "Rational" {
				currEx = curr.EvalRational(es)
			} else if headStr == "Array" {
				currEx = curr.EvalArray(es)
			} else if headStr == "Cases" {
				currEx = curr.EvalCases(es)
			} else if headStr == "NumberQ" {
				currEx = curr.EvalNumberQ(es)
			}
		} else if isPureFunction {
			currEx = pureFunction.EvalFunction(es, curr.Parts[1:])
		}
		if IsSameQ(currEx, lastEx, &es.CASLogger) {
			shouldEval = false
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
						&Integer{big.NewInt(int64(i+1))},
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
					cl.Debugf("r.Parts[1] is Orderless. Now running CommutativeReplace")
					replaced := this.Parts[1:len(this.Parts)]
					CommutativeReplace(&replaced, lhsExpr.Parts[1:len(lhsExpr.Parts)], r.Parts[2], cl)
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

func (this *Expression) String() string {
	headAsSym, isHeadSym := this.Parts[0].(*Symbol)
	fullForm := false
	if isHeadSym && !fullForm {
		res, ok := "", false
		headStr := headAsSym.Name
		if headStr == "Times" {
			return this.ToStringTimes()
		} else if headStr == "Plus" {
			return this.ToStringPlus()
		} else if headStr == "Power" {
			return this.ToStringPower()
		} else if headStr == "Equal" {
			return this.ToStringEqual()
		} else if headStr == "SameQ" {
			return this.ToStringSameQ()
		} else if headStr == "ReplaceAll" {
			return this.ToStringReplaceAll()
		} else if headStr == "ReplaceRepeated" {
			return this.ToStringReplaceRepeated()
		} else if headStr == "Pattern" {
			return this.ToStringPattern()
		} else if headStr == "Blank" {
			ok, res = this.ToStringBlank()
		} else if headStr == "BlankSequence" {
			ok, res = this.ToStringBlankSequence()
		} else if headStr == "BlankNullSequence" {
			ok, res = this.ToStringBlankNullSequence()
		} else if headStr == "Rule" {
			return this.ToStringRule()
		} else if headStr == "RuleDelayed" {
			return this.ToStringRuleDelayed()
		} else if headStr == "Set" {
			return this.ToStringSet()
		} else if headStr == "SetDelayed" {
			return this.ToStringSetDelayed()
		} else if headStr == "List" {
			return this.ToStringList()
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
		buffer.WriteString(e.String())
		if i != len(this.Parts)-1 {
			buffer.WriteString(", ")
		}
	}
	buffer.WriteString("]")
	return buffer.String()
}

func IsAttribute(sm *Symbol, attr string, es *EvalState) bool {
	if sm.Name == "MemberQ" {
		return attr == "Protected"
	} else if sm.Name == "Attributes" {
		return attr == "Protected" || attr == "HoldAll" || attr == "Listable"
	} else if sm.Name == "List" {
		return attr == "Protected" || attr == "Locked"
	} else if sm.Name == "Pattern" {
		return attr == "Protected" || attr == "HoldFirst"
	} else if sm.Name == "Blank" {
		return attr == "Protected"
	} else if sm.Name == "Rule" {
		return attr == "Protected" || attr == "SequenceHold"
	} else if sm.Name == "Times" || sm.Name == "Plus" {
		return attr == "Flat" || attr == "Listable" || attr == "NumericFunction" || attr == "OneIdentity" || attr == "Orderless" || attr == "Protected"
	} else if sm.Name == "Power" {
		return attr == "Listable" || attr == "NumericFunction" || attr == "OneIdentity" || attr == "Protected"
	} else if sm.Name == "ReplaceRepeated" {
		return attr == "Protected"
	} else if sm.Name == "Equal" {
		return attr == "Protected"
	} // This is probably slow because it requires tons of Defined copies
	fmt.Printf("IsAttribute(%v, %v)\n", sm.Name, attr)
	res := (&Expression{[]Ex{
		&Symbol{"MemberQ"},
		&Expression{[]Ex{
			&Symbol{"Attributes"},
			sm,
		}},
		&Symbol{attr},
	}}).Eval(es)
	resSym, resIsSym := res.(*Symbol)
	if resIsSym {
		return resSym.Name == "True"
	}
	return false
}

// TODO: convert to a map
func IsOrderless(sym *Symbol) bool {
	if sym.Name == "Times" {
		return true
	} else if sym.Name == "Plus" {
		return true
	}
	return false
}

// TODO: convert to a map
func IsHoldFirst(sym *Symbol) bool {
	if sym.Name == "Set" {
		return true
	} else if sym.Name == "Pattern" {
		return true
	}
	return false
}

// TODO: convert to a map
func IsHoldRest(sym *Symbol) bool {
	if sym.Name == "If" {
		return true
	} else if sym.Name == "RuleDelayed" {
		return true
	}
	return false
}

// TODO: convert to a map
func IsHoldAll(sym *Symbol) bool {
	if sym.Name == "SetDelayed" {
		return true
	}
	if sym.Name == "Table" {
		return true
	}
	if sym.Name == "Clear" {
		return true
	}
	if sym.Name == "Timing" {
		return true
	}
	if sym.Name == "Hold" {
		return true
	}
	if sym.Name == "CompoundExpression" {
		return true
	}
	return false
}

func (this *Expression) IsEqual(otherEx Ex, cl *CASLogger) string {
	//thisEvaled := this.Eval(es)
	//otherEx = otherEx.Eval(es)
	//this, ok := thisEvaled.(*Expression)
	//if !ok {
		//return thisEvaled.IsEqual(otherEx, cl)
	//}

	other, ok := otherEx.(*Expression)
	if !ok {
		return "EQUAL_UNK"
	}

	thisSym, thisSymOk := this.Parts[0].(*Symbol)
	otherSym, otherSymOk := other.Parts[0].(*Symbol)
	if thisSymOk && otherSymOk {
		if thisSym.Name == otherSym.Name {
			if IsOrderless(thisSym) {
				return CommutativeIsEqual(this.Parts[1:len(this.Parts)], other.Parts[1:len(other.Parts)], cl)
			}
		}
	}

	return FunctionIsEqual(this.Parts, other.Parts, cl)
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

// Apply
func (this *Expression) EvalApply(es *EvalState) Ex {
	if len(this.Parts) != 3 {
		return this
	}

	sym, isSym := this.Parts[1].(*Symbol)
	list, isList := HeadAssertion(this.Parts[2].DeepCopy(), "List")
	if isSym && isList {
		toReturn := &Expression{[]Ex{sym}}
		toReturn.Parts = append(toReturn.Parts, list.Parts[1:]...)
		return toReturn.Eval(es)
	}
	return this.Parts[2]
}
