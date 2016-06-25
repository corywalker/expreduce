package cas

import "bytes"

type Equal struct {
	Lhs Ex
	Rhs Ex
}

func (this *Equal) Eval(es *EvalState) Ex {
	var isequal string = this.Lhs.Eval(es).IsEqual(this.Rhs.Eval(es), es)
	if isequal == "EQUAL_UNK" {
		return this
	} else if isequal == "EQUAL_TRUE" {
		return &Symbol{"True"}
	} else if isequal == "EQUAL_FALSE" {
		return &Symbol{"False"}
	}

	return &Error{"Unexpected equality return value."}
}

func (this *Equal) ToString() string {
	var buffer bytes.Buffer
	buffer.WriteString("(")
	buffer.WriteString(this.Lhs.ToString())
	buffer.WriteString(") == (")
	buffer.WriteString(this.Rhs.ToString())
	buffer.WriteString(")")
	return buffer.String()
}

func (this *Equal) IsEqual(otherEx Ex, es *EvalState) string {
	return "EQUAL_UNK"
}

func (this *Equal) DeepCopy() Ex {
	return &Equal{
		this.Lhs.DeepCopy(),
		this.Rhs.DeepCopy(),
	}
}

type SameQ struct {
	Lhs Ex
	Rhs Ex
}

func (this *SameQ) Eval(es *EvalState) Ex {
	var isequal string = this.Lhs.Eval(es).IsEqual(this.Rhs.Eval(es), es)
	if isequal == "EQUAL_UNK" {
		return &Symbol{"False"}
	} else if isequal == "EQUAL_TRUE" {
		return &Symbol{"True"}
	} else if isequal == "EQUAL_FALSE" {
		return &Symbol{"False"}
	}

	return &Error{"Unexpected equality return value."}
}

func (this *SameQ) ToString() string {
	var buffer bytes.Buffer
	buffer.WriteString("(")
	buffer.WriteString(this.Lhs.ToString())
	buffer.WriteString(") === (")
	buffer.WriteString(this.Rhs.ToString())
	buffer.WriteString(")")
	return buffer.String()
}

func (this *SameQ) IsEqual(otherEx Ex, es *EvalState) string {
	return "EQUAL_UNK"
}

func (this *SameQ) DeepCopy() Ex {
	return &SameQ{
		this.Lhs.DeepCopy(),
		this.Rhs.DeepCopy(),
	}
}
