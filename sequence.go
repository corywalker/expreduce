package cas

import "bytes"

type Sequence struct {
	Arguments []Ex
}

func (this *Sequence) Eval(es *EvalState) Ex {
	return this
}

func (this *Sequence) Replace(r *Rule, es *EvalState) Ex {
	if this.IsMatchQ(r.Lhs, es) {
		return r.Rhs.Eval(es)
	}
	for i := range this.Arguments {
		this.Arguments[i] = this.Arguments[i].Replace(r, es)
	}
	return this.Eval(es)
}

func (this *Sequence) ToString() string {
	var buffer bytes.Buffer
	buffer.WriteString("Sequence[")
	for i, e := range this.Arguments {
		buffer.WriteString(e.ToString())
		if i != len(this.Arguments)-1 {
			buffer.WriteString(", ")
		}
	}
	buffer.WriteString("]")
	return buffer.String()
}

func (this *Sequence) IsEqual(otherEx Ex, es *EvalState) string {
	other, ok := otherEx.(*Sequence)
	if !ok {
		return "EQUAL_UNK"
	}
	return FunctionIsEqual(this.Arguments, other.Arguments, es)
}

func (this *Sequence) IsSameQ(otherEx Ex, es *EvalState) bool {
	other, ok := otherEx.(*Sequence)
	if !ok {
		return false
	}
	// Incredible hack. I need to be using the new Expression representation
	return FunctionIsSameQ(this.Arguments, other.Arguments, es)
}

func (this *Sequence) IsMatchQ(otherEx Ex, es *EvalState) bool {
	other, ok := otherEx.(*Sequence)
	if !ok {
		return false
	}
	return NonCommutativeIsMatchQ(this.Arguments, other.Arguments, es)
}

func (this *Sequence) DeepCopy() Ex {
	var thiscopy = &Sequence{}
	for i := range this.Arguments {
		thiscopy.Arguments = append(thiscopy.Arguments, this.Arguments[i].DeepCopy())
	}
	return thiscopy
}
