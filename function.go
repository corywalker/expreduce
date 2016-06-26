package cas

import "bytes"

type Function struct {
	Name string
	Arguments []Ex
}

func (this *Function) Eval(es *EvalState) Ex {
	if this.Name == "Power" && len(this.Arguments) == 2 {
		t := &Power{
			Base: this.Arguments[0],
			Power: this.Arguments[1],
		}
		return t.Eval(es)
	}
	if this.Name == "Equal" && len(this.Arguments) == 2 {
		t := &Equal{
			Lhs: this.Arguments[0],
			Rhs: this.Arguments[1],
		}
		return t.Eval(es)
	}
	if this.Name == "SameQ" && len(this.Arguments) == 2 {
		t := &Equal{
			Lhs: this.Arguments[0],
			Rhs: this.Arguments[1],
		}
		return t.Eval(es)
	}
	if this.Name == "Plus" {
		t := &Plus{Addends: this.Arguments}
		return t.Eval(es)
	}
	if this.Name == "Times" {
		t := &Times{Multiplicands: this.Arguments}
		return t.Eval(es)
	}
	if this.Name == "Set" && len(this.Arguments) == 2 {
		t := &Set{
			Lhs: this.Arguments[0],
			Rhs: this.Arguments[1],
		}
		return t.Eval(es)
	}
	if this.Name == "SetDelayed" && len(this.Arguments) == 2 {
		t := &SetDelayed{
			Lhs: this.Arguments[0],
			Rhs: this.Arguments[1],
		}
		return t.Eval(es)
	}
	if this.Name == "If" && len(this.Arguments) == 3 {
		t := &If{
			Condition: this.Arguments[0],
			T: this.Arguments[1],
			F: this.Arguments[2],
		}
		return t.Eval(es)
	}
	if this.Name == "While" && len(this.Arguments) == 1 {
		t := &While{
			Test: this.Arguments[0],
			Body: &Symbol{"Null"},
		}
		return t.Eval(es)
	}
	if this.Name == "While" && len(this.Arguments) == 2 {
		t := &While{
			Test: this.Arguments[0],
			Body: this.Arguments[1],
		}
		return t.Eval(es)
	}
	if this.Name == "MatchQ" && len(this.Arguments) == 2 {
		t := &MatchQ{
			Expr: this.Arguments[0],
			Form: this.Arguments[1],
		}
		return t.Eval(es)
	}
	if this.Name == "Replace" && len(this.Arguments) == 2 {
		t := &Replace{
			Expr: this.Arguments[0],
			Rules: this.Arguments[1],
		}
		return t.Eval(es)
	}
	return this
}

func (this *Function) Replace(r *Rule, es *EvalState) Ex {
	if this.IsMatchQ(r.Lhs, es) {
		return r.Rhs
	}
	for i := range this.Arguments {
		this.Arguments[i] = this.Arguments[i].Replace(r, es)
	}
	return this.Eval(es)
}

func (this *Function) ToString() string {
	var buffer bytes.Buffer
	buffer.WriteString(this.Name)
	buffer.WriteString("[")
	for i, e := range this.Arguments {
		buffer.WriteString(e.ToString())
		if i != len(this.Arguments)-1 {
			buffer.WriteString(", ")
		}
	}
	buffer.WriteString("]")
	return buffer.String()
}

func (this *Function) IsEqual(otherEx Ex, es *EvalState) string {
	other, ok := otherEx.(*Function)
	if !ok {
		return "EQUAL_UNK"
	}
	return FunctionIsEqual(this.Arguments, other.Arguments, es)
}

func (this *Function) IsSameQ(otherEx Ex, es *EvalState) bool {
	other, ok := otherEx.(*Function)
	if !ok {
		return false
	}
	if this.Name != other.Name {
		return false
	}
	return FunctionIsSameQ(this.Arguments, other.Arguments, es)
}

func (this *Function) IsMatchQ(otherEx Ex, es *EvalState) bool {
	return this.IsSameQ(otherEx, es)
}

func (this *Function) DeepCopy() Ex {
	var thiscopy = &Function{}
	thiscopy.Name = this.Name
	for i := range this.Arguments {
		thiscopy.Arguments = append(thiscopy.Arguments, this.Arguments[i].DeepCopy())
	}
	return thiscopy
}
