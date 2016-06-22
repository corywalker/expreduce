package cas

import "bytes"

// An exponent expression with a base and an exponent
type Power struct {
	Base Ex
	Power Ex
}

func (this *Power) Eval(es *EvalState) Ex {
	// Start by evaluating each part
	this.Base = this.Base.Eval(es)
	this.Power = this.Power.Eval(es)

	// TODO: Handle cases like float raised to the float and things raised to
	// zero and 1

	return this
}

func (this *Power) ToString() string {
	var buffer bytes.Buffer
	buffer.WriteString(this.Base.ToString())
	buffer.WriteString("^")
	buffer.WriteString(this.Power.ToString())
	return buffer.String()
}

func (this *Power) IsEqual(otherEx Ex, es *EvalState) string {
	thisEx := this.Eval(es)
	otherEx = otherEx.Eval(es)
	this, ok := thisEx.(*Power)
	if !ok {
		return thisEx.IsEqual(otherEx, es)
	}
	other, ok := otherEx.(*Power)
	if !ok {
		return "EQUAL_FALSE"
	}
	// TODO: Could be improved by knowing about base conversions and logarithms
	var baseEqual = this.Base.IsEqual(other.Base, es) == "EQUAL_TRUE"
	var exponentEqual = this.Power.IsEqual(other.Power, es) == "EQUAL_TRUE"

	if baseEqual && exponentEqual {
		return "EQUAL_TRUE"
	}
	return "EQUAL_UNK"
}

func (this *Power) DeepCopy() Ex {
	return &Power{
		this.Base.DeepCopy(),
		this.Power.DeepCopy(),
	}
}
