package cas

import "bytes"

type Function struct {
	Name string
	Arguments []Ex
}

func (this *Function) Eval(es *EvalState) Ex {
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
