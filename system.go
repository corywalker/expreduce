package cas

import "bytes"

type SetLogging struct {
	Expr Ex
}

func (this *SetLogging) Eval(es *EvalState) Ex {
	sym, ok := this.Expr.(*Symbol)
	if ok {
		if sym.Name == "True" {
			es.DebugOn()
			return &Symbol{"Null"}
		} else if sym.Name == "False" {
			es.DebugOff()
			return &Symbol{"Null"}
		}
	}
	return this
}

func (this *SetLogging) Replace(r *Rule, es *EvalState) Ex {
	if this.IsMatchQ(r.Lhs, es) {
		return r.Rhs
	}
	this.Expr = this.Expr.Replace(r, es)
	return this.Eval(es)
}

func (this *SetLogging) ToString() string {
	var buffer bytes.Buffer
	buffer.WriteString("SetLogging[")
	buffer.WriteString(this.Expr.ToString())
	buffer.WriteString("]")
	return buffer.String()
}

func (this *SetLogging) IsEqual(otherEx Ex, es *EvalState) string {
	other, ok := otherEx.(*SetLogging)
	if !ok {
		return "EQUAL_UNK"
	}
	return FunctionIsEqual([]Ex{
		this.Expr,
	}, []Ex{
		other.Expr,
	}, es)
}

func (this *SetLogging) IsSameQ(otherEx Ex, es *EvalState) bool {
	other, ok := otherEx.(*SetLogging)
	if !ok {
		return false
	}
	return FunctionIsSameQ([]Ex{
		this.Expr,
	}, []Ex{
		other.Expr,
	}, es)
}

func (this *SetLogging) IsMatchQ(otherEx Ex, es *EvalState) bool {
	if IsBlankType(otherEx, "SetLogging") {
		return true
	}
	return this.IsSameQ(otherEx, es)
}

func (this *SetLogging) DeepCopy() Ex {
	return &SetLogging{
		Expr: this.Expr.DeepCopy(),
	}
}
