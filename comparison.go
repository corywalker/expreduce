package cas

import "bytes"

type Equal struct {
	Lhs Ex
	Rhs Ex
}

func (this *Equal) Eval(es *EvalState) Ex {
	var isequal string = this.Lhs.IsEqual(this.Rhs, es)
	if isequal == "EQUAL_UNK" {
		return &Error{"Encountered EQUAL_UNK when comparing for the Equal."}
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

type If struct {
	Condition Ex
	T Ex
	F Ex
}

func (this *If) Eval(es *EvalState) Ex {
	var isequal string = this.Condition.IsEqual(&Symbol{"True"}, es)
	if isequal == "EQUAL_UNK" {
		return &Error{"Encountered EQUAL_UNK when comparing for the Is."}
	} else if isequal == "EQUAL_TRUE" {
		return this.T
	} else if isequal == "EQUAL_FALSE" {
		return this.F
	}

	return &Error{"Unexpected equality return value."}
}

func (this *If) ToString() string {
	var buffer bytes.Buffer
	buffer.WriteString("If[")
	buffer.WriteString(this.Condition.ToString())
	buffer.WriteString(", ")
	buffer.WriteString(this.T.ToString())
	buffer.WriteString(", ")
	buffer.WriteString(this.F.ToString())
	buffer.WriteString("]")
	return buffer.String()
}

func (this *If) IsEqual(otherEx Ex, es *EvalState) string {
	return "EQUAL_UNK"
}

func (this *If) DeepCopy() Ex {
	return &If{
		Condition: this.Condition.DeepCopy(),
		T: this.T.DeepCopy(),
		F: this.F.DeepCopy(),
	}
}
