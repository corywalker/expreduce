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
	for i := range this.Parts {
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
		seq, isseq := e.(*Sequence)
		if isseq {
			start := j
			end := j + 1
			if j == 0 {
				this.Parts = append(seq.Arguments, this.Parts[end:]...)
			} else if j == len(this.Parts)-1 {
				this.Parts = append(this.Parts[:start], seq.Arguments...)
			} else {
				// All of these deep copies may not be needed.
				this.Parts = append(append(this.DeepCopy().(*Expression).Parts[:start], seq.DeepCopy().(*Sequence).Arguments...), this.DeepCopy().(*Expression).Parts[end:]...)
			}
			offset += len(seq.Arguments) - 1
		}
	}

	headAsSym, isHeadSym := this.Parts[0].(*Symbol)
	if isHeadSym {
		headStr := headAsSym.Name
		args := this.Parts[1:len(this.Parts)]
		if headStr == "Power" && len(args) == 2 {
			return this.EvalPower(es)
		}
		if headStr == "Equal" && len(args) == 2 {
			t := &Equal{
				Lhs: args[0],
				Rhs: args[1],
			}
			return t.Eval(es)
		}
		if headStr == "SameQ" && len(args) == 2 {
			t := &Equal{
				Lhs: args[0],
				Rhs: args[1],
			}
			return t.Eval(es)
		}
		if headStr == "Plus" {
			return this.EvalPlus(es)
		}
		if headStr == "Times" {
			return this.EvalTimes(es)
		}
		if headStr == "Set" && len(args) == 2 {
			t := &Set{
				Lhs: args[0],
				Rhs: args[1],
			}
			return t.Eval(es)
		}
		if headStr == "SetDelayed" && len(args) == 2 {
			t := &SetDelayed{
				Lhs: args[0],
				Rhs: args[1],
			}
			return t.Eval(es)
		}
		if headStr == "If" && len(args) == 3 {
			t := &If{
				Condition: args[0],
				T:         args[1],
				F:         args[2],
			}
			return t.Eval(es)
		}
		if headStr == "While" && len(args) == 1 {
			t := &While{
				Test: args[0],
				Body: &Symbol{"Null"},
			}
			return t.Eval(es)
		}
		if headStr == "While" && len(args) == 2 {
			t := &While{
				Test: args[0],
				Body: args[1],
			}
			return t.Eval(es)
		}
		if headStr == "MatchQ" && len(args) == 2 {
			t := &MatchQ{
				Expr: args[0],
				Form: args[1],
			}
			return t.Eval(es)
		}
		if headStr == "Replace" && len(args) == 2 {
			t := &Replace{
				Expr:  args[0],
				Rules: args[1],
			}
			return t.Eval(es)
		}
		if headStr == "BasicSimplify" && len(args) == 1 {
			t := &BasicSimplify{
				Expr: args[0],
			}
			return t.Eval(es)
		}
		if headStr == "SetLogging" && len(args) == 1 {
			t := &SetLogging{
				Expr: args[0],
			}
			return t.Eval(es)
		}
		if headStr == "Definition" && len(args) == 1 {
			t := &Definition{
				Expr: args[0],
			}
			return t.Eval(es)
		}
		if headStr == "Sequence" {
			t := &Sequence{Arguments: args}
			return t.Eval(es)
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

func IsOrderless(sym *Symbol) bool {
	if sym.Name == "Times" {
		return true
	} else if sym.Name == "Plus" {
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
		if IsBlankTypeCapturing(otherEx, this, headStr, es) {
			return true
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
