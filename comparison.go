package cas

import "bytes"

type EqualQ struct {
	lhs Ex
	rhs Ex
}

func (this *EqualQ) Eval() Ex {
	var isequal string = this.lhs.IsEqual(this.rhs)
	if isequal == "EQUAL_UNK" {
		return &Error{"Encountered EQUAL_UNK when comparing for the EqualQ."}
	} else if isequal == "EQUAL_TRUE" {
		return &Bool{true}
	} else if isequal == "EQUAL_FALSE" {
		return &Bool{false}
	}

	return &Error{"Unexpected equality return value."}
}

func (this *EqualQ) ToString() string {
	var buffer bytes.Buffer
	buffer.WriteString(this.lhs.ToString())
	buffer.WriteString(" == ")
	buffer.WriteString(this.rhs.ToString())
	return buffer.String()
}

func (this *EqualQ) IsEqual(otherEx Ex) string {
	return "EQUAL_UNK"
}
