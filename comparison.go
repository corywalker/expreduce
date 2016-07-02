package cas

import "bytes"

type Equal struct {
	Lhs Ex
	Rhs Ex
}

func (this *Equal) Eval(es *EvalState) Ex {
	var isequal string = this.Lhs.Eval(es).IsEqual(this.Rhs.Eval(es), es)
	if isequal == "EQUAL_UNK" {
		return this
	} else if isequal == "EQUAL_TRUE" {
		return &Symbol{"True"}
	} else if isequal == "EQUAL_FALSE" {
		return &Symbol{"False"}
	}

	return &Error{"Unexpected equality return value."}
}

func (this *Equal) Replace(r *Rule, es *EvalState) Ex {
	if this.IsMatchQ(r.Lhs, es) {
		return r.Rhs
	}
	this.Lhs = this.Lhs.Replace(r, es)
	this.Rhs = this.Rhs.Replace(r, es)
	return this.Eval(es)
}

func (this *Equal) ToString() string {
	var buffer bytes.Buffer
	buffer.WriteString("(")
	buffer.WriteString(this.Lhs.ToString())
	buffer.WriteString(") == (")
	buffer.WriteString(this.Rhs.ToString())
	buffer.WriteString(")")
	return buffer.String()
}

func (this *Equal) IsEqual(otherEx Ex, es *EvalState) string {
	other, ok := otherEx.(*Equal)
	if !ok {
		return "EQUAL_UNK"
	}
	return FunctionIsEqual([]Ex{
		this.Lhs,
		this.Rhs,
	}, []Ex{
		other.Lhs,
		other.Rhs,
	}, es)
}

func (this *Equal) IsSameQ(otherEx Ex, es *EvalState) bool {
	other, ok := otherEx.(*Equal)
	if !ok {
		return false
	}
	return FunctionIsSameQ([]Ex{
		this.Lhs,
		this.Rhs,
	}, []Ex{
		other.Lhs,
		other.Rhs,
	}, es)
}

func (this *Equal) IsMatchQ(otherEx Ex, es *EvalState) bool {
	if IsBlankType(otherEx, "Equal") {
		return true
	}
	return this.IsSameQ(otherEx, es)
}

func (this *Equal) DeepCopy() Ex {
	return &Equal{
		this.Lhs.DeepCopy(),
		this.Rhs.DeepCopy(),
	}
}

type SameQ struct {
	Lhs Ex
	Rhs Ex
}

func (this *SameQ) Eval(es *EvalState) Ex {
	var issame bool = this.Lhs.Eval(es).IsSameQ(this.Rhs.Eval(es), es)
	if issame {
		return &Symbol{"True"}
	} else {
		return &Symbol{"False"}
	}
}

func (this *SameQ) Replace(r *Rule, es *EvalState) Ex {
	if this.IsMatchQ(r.Lhs, es) {
		return r.Rhs
	}
	this.Lhs = this.Lhs.Replace(r, es)
	this.Rhs = this.Rhs.Replace(r, es)
	return this.Eval(es)
}

func (this *SameQ) ToString() string {
	var buffer bytes.Buffer
	buffer.WriteString("(")
	buffer.WriteString(this.Lhs.ToString())
	buffer.WriteString(") === (")
	buffer.WriteString(this.Rhs.ToString())
	buffer.WriteString(")")
	return buffer.String()
}

func (this *SameQ) IsEqual(otherEx Ex, es *EvalState) string {
	return "EQUAL_UNK"
}

func (this *SameQ) IsSameQ(otherEx Ex, es *EvalState) bool {
	return false
}

func (this *SameQ) IsMatchQ(otherEx Ex, es *EvalState) bool {
	return this.IsSameQ(otherEx, es)
}

func (this *SameQ) DeepCopy() Ex {
	return &SameQ{
		this.Lhs.DeepCopy(),
		this.Rhs.DeepCopy(),
	}
}

type MatchQ struct {
	Expr Ex
	Form Ex
}

func (this *MatchQ) Eval(es *EvalState) Ex {
	var issame bool = this.Expr.Eval(es).IsMatchQ(this.Form.Eval(es), es)
	if issame {
		return &Symbol{"True"}
	} else {
		return &Symbol{"False"}
	}
}

func (this *MatchQ) Replace(r *Rule, es *EvalState) Ex {
	if this.IsMatchQ(r.Lhs, es) {
		return r.Rhs
	}
	this.Expr = this.Expr.Replace(r, es)
	this.Form = this.Form.Replace(r, es)
	return this.Eval(es)
}

func (this *MatchQ) ToString() string {
	var buffer bytes.Buffer
	buffer.WriteString("MatchQ[")
	buffer.WriteString(this.Expr.ToString())
	buffer.WriteString(", ")
	buffer.WriteString(this.Form.ToString())
	buffer.WriteString("]")
	return buffer.String()
}

func (this *MatchQ) IsEqual(otherEx Ex, es *EvalState) string {
	return "EQUAL_UNK"
}

func (this *MatchQ) IsSameQ(otherEx Ex, es *EvalState) bool {
	return false
}

func (this *MatchQ) IsMatchQ(otherEx Ex, es *EvalState) bool {
	return this.IsSameQ(otherEx, es)
}

func (this *MatchQ) DeepCopy() Ex {
	return &MatchQ{
		this.Expr.DeepCopy(),
		this.Form.DeepCopy(),
	}
}
