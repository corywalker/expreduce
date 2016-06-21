package cas

import "bytes"

// An exponent expression with a base and an exponent
type Exponent struct {
	Base Ex
	Exponent Ex
}

func (this *Exponent) Eval(es *EvalState) Ex {
	// Start by evaluating each part
	this.Base = this.Base.Eval(es)
	this.Exponent = this.Exponent.Eval(es)

	// TODO: Handle cases like float raised to the float and things raised to
	// zero and 1

	return this
}

func (this *Exponent) ToString() string {
	var buffer bytes.Buffer
	buffer.WriteString(this.Base.ToString())
	buffer.WriteString("^")
	buffer.WriteString(this.Exponent.ToString())
	return buffer.String()
}

func (this *Exponent) IsEqual(otherEx Ex, es *EvalState) string {
	thisEx := this.Eval(es)
	otherEx = otherEx.Eval(es)
	this, ok := thisEx.(*Exponent)
	if !ok {
		return thisEx.IsEqual(otherEx, es)
	}
	other, ok := otherEx.(*Exponent)
	if !ok {
		return "EQUAL_FALSE"
	}
	// TODO: Could be improved by knowing about base conversions and logarithms
	var baseEqual = this.Base.IsEqual(other.Base, es) == "EQUAL_TRUE"
	var exponentEqual = this.Exponent.IsEqual(other.Exponent, es) == "EQUAL_TRUE"

	if baseEqual && exponentEqual {
		return "EQUAL_TRUE"
	}
	return "EQUAL_UNK"
}
