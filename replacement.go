package cas

import "bytes"

type Rule struct {
	Lhs Ex
	Rhs Ex
}

func (this *Rule) Eval(es *EvalState) Ex {
	this.Lhs = this.Lhs.Eval(es)
	this.Rhs = this.Rhs.Eval(es)
	return this
}

func (this *Rule) Replace(r *Rule, es *EvalState) Ex {
	if this.IsMatchQ(r.Lhs, es) {
		return r.Rhs
	}
	return this
}

func (this *Rule) ToString() string {
	var buffer bytes.Buffer
	buffer.WriteString("(")
	buffer.WriteString(this.Lhs.ToString())
	buffer.WriteString(") -> (")
	buffer.WriteString(this.Rhs.ToString())
	buffer.WriteString(")")
	return buffer.String()
}

func (this *Rule) IsEqual(otherEx Ex, es *EvalState) string {
	other, ok := otherEx.(*Rule)
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

func (this *Rule) IsSameQ(otherEx Ex, es *EvalState) bool {
	other, ok := otherEx.(*Rule)
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

func (this *Rule) IsMatchQ(otherEx Ex, es *EvalState) bool {
	if IsBlankType(otherEx, "Rule") {
		return true
	}
	return this.IsSameQ(otherEx, es)
}

func (this *Rule) DeepCopy() Ex {
	return &Rule{
		this.Lhs.DeepCopy(),
		this.Rhs.DeepCopy(),
	}
}

type Replace struct {
	Expr  Ex
	Rules Ex
}

func (this *Replace) Eval(es *EvalState) Ex {
	this.Expr = this.Expr.Eval(es)
	this.Rules = this.Rules.Eval(es)
	//_, ok := this.Rules.(*Rule)
	rulesRule, ok := this.Rules.(*Rule)
	if ok {
		oldVars := es.GetDefinedSnapshot()
		newEx := this.Expr.Replace(rulesRule, es)
		es.ClearPD()
		newEx = newEx.Eval(es)
		es.defined = oldVars
		return newEx
		//return this
	}
	return this
}

func (this *Replace) Replace(r *Rule, es *EvalState) Ex {
	if this.IsMatchQ(r.Lhs, es) {
		return r.Rhs
	}
	this.Expr = this.Expr.Replace(r, es)
	this.Rules = this.Rules.Replace(r, es)
	return this.Eval(es)
}

func (this *Replace) ToString() string {
	var buffer bytes.Buffer
	buffer.WriteString("(")
	buffer.WriteString(this.Expr.ToString())
	buffer.WriteString(") /. (")
	buffer.WriteString(this.Rules.ToString())
	buffer.WriteString(")")
	return buffer.String()
}

func (this *Replace) IsEqual(otherEx Ex, es *EvalState) string {
	other, ok := otherEx.(*Replace)
	if !ok {
		return "EQUAL_UNK"
	}
	return FunctionIsEqual([]Ex{
		this.Expr,
		this.Rules,
	}, []Ex{
		other.Expr,
		other.Rules,
	}, es)
}

func (this *Replace) IsSameQ(otherEx Ex, es *EvalState) bool {
	other, ok := otherEx.(*Replace)
	if !ok {
		return false
	}
	return FunctionIsSameQ([]Ex{
		this.Expr,
		this.Rules,
	}, []Ex{
		other.Expr,
		other.Rules,
	}, es)
}

func (this *Replace) IsMatchQ(otherEx Ex, es *EvalState) bool {
	return this.IsSameQ(otherEx, es)
}

func (this *Replace) DeepCopy() Ex {
	return &Replace{
		this.Expr.DeepCopy(),
		this.Rules.DeepCopy(),
	}
}
