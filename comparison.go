package cas

import "bytes"

type EqualQ struct {
	Lhs Ex
	Rhs Ex
}

func (this *EqualQ) Eval(es *EvalState) Ex {
	var isequal string = this.Lhs.IsEqual(this.Rhs, es)
	if isequal == "EQUAL_UNK" {
		return &Error{"Encountered EQUAL_UNK when comparing for the EqualQ."}
	} else if isequal == "EQUAL_TRUE" {
		return &Symbol{"True"}
	} else if isequal == "EQUAL_FALSE" {
		return &Symbol{"False"}
	}

	return &Error{"Unexpected equality return value."}
}

func (this *EqualQ) ToString() string {
	var buffer bytes.Buffer
	buffer.WriteString("(")
	buffer.WriteString(this.Lhs.ToString())
	buffer.WriteString(") == (")
	buffer.WriteString(this.Rhs.ToString())
	buffer.WriteString(")")
	return buffer.String()
}

func (this *EqualQ) IsEqual(otherEx Ex, es *EvalState) string {
	return "EQUAL_UNK"
}

func (this *EqualQ) DeepCopy() Ex {
	return &EqualQ{
		this.Lhs.DeepCopy(),
		this.Rhs.DeepCopy(),
	}
}
