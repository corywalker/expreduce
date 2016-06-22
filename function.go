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
	return this
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
	return "EQUAL_UNK"
}

func (this *Function) DeepCopy() Ex {
	var thiscopy = &Function{}
	thiscopy.Name = this.Name
	for i := range this.Arguments {
		thiscopy.Arguments = append(thiscopy.Arguments, this.Arguments[i].DeepCopy())
	}
	return thiscopy
}
