package cas

import "bytes"

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

func (this *Expression) Eval(es *EvalState) Ex {
	// Start by evaluating each argument
	headSym, headIsSym := &Symbol{}, false
	if len(this.Parts) > 0 {
		headSym, headIsSym = this.Parts[0].(*Symbol)
	}
	for i := range this.Parts {
		if headIsSym && i ==  1 && IsHoldFirst(headSym) {
			continue
		}
		if headIsSym && IsHoldAll(headSym) {
			continue
		}
		this.Parts[i] = this.Parts[i].Eval(es)
	}

	// If any of the parts are Sequence, merge them with parts
	// TODO: I should not be attempting to merge the head if it happens to be
	// a Sequence type
	origLen := len(this.Parts)
	offset := 0
	for i := 0; i < origLen; i++ {
		j := i + offset
		e := this.Parts[j]
		seq, isseq := HeadAssertion(e, "Sequence")
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

	headAsSym, isHeadSym := this.Parts[0].(*Symbol)
	if isHeadSym {
		headStr := headAsSym.Name
		if headStr == "Power" {
			return this.EvalPower(es)
		}
		if headStr == "Equal" {
			return this.EvalEqual(es)
		}
		if headStr == "SameQ" {
			return this.EvalSameQ(es)
		}
		if headStr == "Plus" {
			return this.EvalPlus(es)
		}
		if headStr == "Times" {
			return this.EvalTimes(es)
		}
		if headStr == "Set" {
			return this.EvalSet(es)
		}
		if headStr == "SetDelayed" {
			return this.EvalSetDelayed(es)
		}
		if headStr == "If" {
			return this.EvalIf(es)
		}
		if headStr == "While" {
			return this.EvalWhile(es)
		}
		if headStr == "MatchQ" {
			return this.EvalMatchQ(es)
		}
		if headStr == "Replace" {
			return this.EvalReplace(es)
		}
		if headStr == "ReplaceRepeated" {
			return this.EvalReplaceRepeated(es)
		}
		if headStr == "BasicSimplify" {
			return this.EvalBasicSimplify(es)
		}
		if headStr == "SetLogging" {
			return this.EvalSetLogging(es)
		}
		if headStr == "Definition" {
			return this.EvalDefinition(es)
		}

		theRes, isDefined := es.GetDef(headStr, this)
		if isDefined {
			return theRes
		}
	}
	return this
}

func (this *Expression) Replace(r *Rule, es *EvalState) Ex {
	oldVars := es.GetDefinedSnapshot()
	es.log.Debugf(es.Pre() + "In Expression.Replace. First trying this.IsMatchQ(r.Lhs, es).")
	es.log.Debugf(es.Pre()+"Rule r is: %s", r.ToString())

	matchq := this.IsMatchQ(r.Lhs, es)
	toreturn := r.Rhs.DeepCopy().Eval(es)
	es.ClearPD()
	es.defined = oldVars
	if matchq {
		es.log.Debugf(es.Pre()+"After MatchQ, rule is: %s", r.ToString())
		es.log.Debugf(es.Pre()+"MatchQ succeeded. Returning r.Rhs: %s", r.Rhs.ToString())
		return toreturn
	}

	thisSym, thisSymOk := this.Parts[0].(*Symbol)
	lhsExpr, lhsExprOk := r.Lhs.(*Expression)
	if lhsExprOk {
		otherSym, otherSymOk := lhsExpr.Parts[0].(*Symbol)
		if thisSymOk && otherSymOk {
			if thisSym.Name == otherSym.Name {
				if IsOrderless(thisSym) {
					es.log.Debugf(es.Pre() + "r.Lhs is Orderless. Now running CommutativeReplace")
					replaced := this.Parts[1:len(this.Parts)]
					CommutativeReplace(&replaced, lhsExpr.Parts[1:len(lhsExpr.Parts)], r.Rhs, es)
					this.Parts = this.Parts[0:1]
					this.Parts = append(this.Parts, replaced...)
				}
			}
		}
	}

	for i := range this.Parts {
		this.Parts[i] = this.Parts[i].Replace(r, es)
	}
	return this.Eval(es)
}

func (this *Expression) ToString() string {
	headAsSym, isHeadSym := this.Parts[0].(*Symbol)
	if isHeadSym {
		headStr := headAsSym.Name
		if headStr == "Times" {
			return this.ToStringTimes()
		} else if headStr == "Plus" {
			return this.ToStringPlus()
		} else if headStr == "Power" {
			return this.ToStringPower()
		} else if headStr == "Equal" {
			return this.ToStringEqual()
		} else if headStr == "Replace" {
			return this.ToStringReplace()
		} else if headStr == "ReplaceRepeated" {
			return this.ToStringReplaceRepeated()
		} else if headStr == "BlankNullSequence" {
			return this.ToStringBlankNullSequence()
		}
	}

	// Default printing format
	var buffer bytes.Buffer
	buffer.WriteString(this.Parts[0].ToString())
	buffer.WriteString("[")
	for i, e := range this.Parts {
		if i == 0 {
			continue
		}
		buffer.WriteString(e.ToString())
		if i != len(this.Parts)-1 {
			buffer.WriteString(", ")
		}
	}
	buffer.WriteString("]")
	return buffer.String()
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
func IsHoldAll(sym *Symbol) bool {
	if sym.Name == "SetDelayed" {
		return true
	}
	return false
}

func (this *Expression) IsEqual(otherEx Ex, es *EvalState) string {
	thisEvaled := this.Eval(es)
	otherEx = otherEx.Eval(es)
	this, ok := thisEvaled.(*Expression)
	if !ok {
		return thisEvaled.IsEqual(otherEx, es)
	}

	other, ok := otherEx.(*Expression)
	if !ok {
		return "EQUAL_UNK"
	}

	thisSym, thisSymOk := this.Parts[0].(*Symbol)
	otherSym, otherSymOk := other.Parts[0].(*Symbol)
	if thisSymOk && otherSymOk {
		if thisSym.Name == otherSym.Name {
			if IsOrderless(thisSym) {
				return CommutativeIsEqual(this.Parts[1:len(this.Parts)], other.Parts[1:len(other.Parts)], es)
			}
		}
	}

	return FunctionIsEqual(this.Parts, other.Parts, es)
}

func (this *Expression) IsSameQ(otherEx Ex, es *EvalState) bool {
	other, ok := otherEx.(*Expression)
	if !ok {
		return false
	}

	thisSym, thisSymOk := this.Parts[0].(*Symbol)
	otherSym, otherSymOk := other.Parts[0].(*Symbol)
	if thisSymOk && otherSymOk {
		if thisSym.Name == otherSym.Name {
			if IsOrderless(thisSym) {
				return this.IsEqual(otherEx, es) == "EQUAL_TRUE"
			}
		}
	}

	return FunctionIsSameQ(this.Parts, other.Parts, es)
}

func (this *Expression) IsMatchQ(otherEx Ex, es *EvalState) bool {
	headAsSym, isHeadSym := this.Parts[0].(*Symbol)
	if isHeadSym {
		headStr := headAsSym.Name
		if IsBlankTypeOnly(otherEx) {
			if IsBlankTypeCapturing(otherEx, this, headStr, es) {
				return true
			}
			return false
		}
	}
	//thisEx := this.Eval(es)
	//otherEx = otherEx.Eval(es)
	//this, ok := thisEx.(*Expression)
	//if !ok {
	//return thisEx.IsMatchQ(otherEx, es)
	//}
	other, otherOk := otherEx.(*Expression)
	if !otherOk {
		return false
	}

	thisSym, thisSymOk := this.Parts[0].(*Symbol)
	otherSym, otherSymOk := other.Parts[0].(*Symbol)
	if thisSymOk && otherSymOk {
		if thisSym.Name == otherSym.Name {
			if IsOrderless(thisSym) {
				return CommutativeIsMatchQ(this.Parts[1:len(this.Parts)], other.Parts[1:len(other.Parts)], es)
			}
		}
	}

	return NonCommutativeIsMatchQ(this.Parts, other.Parts, es)
}

func (this *Expression) DeepCopy() Ex {
	var thiscopy = &Expression{}
	for i := range this.Parts {
		thiscopy.Parts = append(thiscopy.Parts, this.Parts[i].DeepCopy())
	}
	return thiscopy
}
