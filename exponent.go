package cas

import "bytes"

// An exponent expression with a base and an exponent
type Exponent struct {
	base Ex
	exponent Ex
}

func (this *Exponent) Eval() Ex {
	// Start by evaluating each part
	this.base = this.base.Eval()
	this.exponent = this.exponent.Eval()

	// TODO: Handle cases like float raised to the float and things raised to
	// zero and 1

	return this
}

func (this *Exponent) ToString() string {
	var buffer bytes.Buffer
	buffer.WriteString(this.base.ToString())
	buffer.WriteString("^")
	buffer.WriteString(this.exponent.ToString())
	return buffer.String()
}

func (this *Exponent) IsEqual(otherEx Ex) string {
	thisEx := this.Eval()
	otherEx = otherEx.Eval()
	this, ok := thisEx.(*Exponent)
	if !ok {
		return thisEx.IsEqual(otherEx)
	}
	other, ok := otherEx.(*Exponent)
	if !ok {
		return "EQUAL_FALSE"
	}
	// TODO: Could be improved by knowing about base conversions and logarithms
	var baseEqual = this.base.IsEqual(other.base) == "EQUAL_TRUE"
	var exponentEqual = this.exponent.IsEqual(other.exponent) == "EQUAL_TRUE"

	if baseEqual && exponentEqual {
		return "EQUAL_TRUE"
	}
	return "EQUAL_UNK"
}
