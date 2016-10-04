package cas

import "bytes"

func (this *Expression) EvalSetLogging(es *EvalState) Ex {
	if len(this.Parts) != 2 {
		return this
	}

	sym, ok := this.Parts[1].(*Symbol)
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

type Definition struct {
	Expr Ex
}

func (this *Definition) Eval(es *EvalState) Ex {
	//sym, ok := this.Expr.(*Symbol)
	return &Error{es.ToString()}
}

func (this *Definition) Replace(r *Rule, es *EvalState) Ex {
	if this.IsMatchQ(r.Lhs, es) {
		return r.Rhs
	}
	this.Expr = this.Expr.Replace(r, es)
	return this.Eval(es)
}

func (this *Definition) ToString() string {
	var buffer bytes.Buffer
	buffer.WriteString("Definition[")
	buffer.WriteString(this.Expr.ToString())
	buffer.WriteString("]")
	return buffer.String()
}

func (this *Definition) IsEqual(otherEx Ex, es *EvalState) string {
	other, ok := otherEx.(*Definition)
	if !ok {
		return "EQUAL_UNK"
	}
	return FunctionIsEqual([]Ex{
		this.Expr,
	}, []Ex{
		other.Expr,
	}, es)
}

func (this *Definition) IsSameQ(otherEx Ex, es *EvalState) bool {
	other, ok := otherEx.(*Definition)
	if !ok {
		return false
	}
	return FunctionIsSameQ([]Ex{
		this.Expr,
	}, []Ex{
		other.Expr,
	}, es)
}

func (this *Definition) IsMatchQ(otherEx Ex, es *EvalState) bool {
	if IsBlankType(otherEx, "Definition") {
		return true
	}
	return this.IsSameQ(otherEx, es)
}

func (this *Definition) DeepCopy() Ex {
	return &Definition{
		Expr: this.Expr.DeepCopy(),
	}
}
