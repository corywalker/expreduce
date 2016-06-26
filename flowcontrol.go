package cas

import "bytes"

type If struct {
	Condition Ex
	T Ex
	F Ex
}

func (this *If) Eval(es *EvalState) Ex {
	var isequal string = this.Condition.Eval(es).IsEqual(&Symbol{"True"}, es)
	if isequal == "EQUAL_UNK" {
		return this
	} else if isequal == "EQUAL_TRUE" {
		return this.T.Eval(es)
	} else if isequal == "EQUAL_FALSE" {
		return this.F.Eval(es)
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
	other, ok := otherEx.(*If)
	if !ok {
		return "EQUAL_UNK"
	}
	return FunctionIsEqual([]Ex{
			this.Condition,
			this.T,
			this.F,
		}, []Ex{
			other.Condition,
			other.T,
			other.F,
		}, es)
}

func (this *If) IsSameQ(otherEx Ex, es *EvalState) bool {
	other, ok := otherEx.(*If)
	if !ok {
		return false
	}
	return FunctionIsSameQ([]Ex{
			this.Condition,
			this.T,
			this.F,
		}, []Ex{
			other.Condition,
			other.T,
			other.F,
		}, es)
}

func (this *If) IsMatchQ(otherEx Ex, es *EvalState) bool {
	return this.IsSameQ(otherEx, es)
}

func (this *If) DeepCopy() Ex {
	return &If{
		Condition: this.Condition.DeepCopy(),
		T: this.T.DeepCopy(),
		F: this.F.DeepCopy(),
	}
}

type While struct {
	Test Ex
	Body Ex
}

func (this *While) Eval(es *EvalState) Ex {
	isequal := this.Test.Eval(es).IsEqual(&Symbol{"True"}, es)
	cont := isequal == "EQUAL_TRUE"
	for cont {

		isequal = this.Test.Eval(es).IsEqual(&Symbol{"True"}, es)
		cont = isequal == "EQUAL_TRUE"
	}

	if isequal == "EQUAL_UNK" {
		return &Error{"Encountered EQUAL_UNK when evaluating test for the While."}
	} else if isequal == "EQUAL_TRUE" {
		return &Symbol{"Null"}
	} else if isequal == "EQUAL_FALSE" {
		return &Symbol{"Null"}
	}

	return &Error{"Unexpected equality return value."}
}

func (this *While) ToString() string {
	var buffer bytes.Buffer
	buffer.WriteString("While[")
	buffer.WriteString(this.Test.ToString())
	buffer.WriteString(", ")
	buffer.WriteString(this.Body.ToString())
	buffer.WriteString("]")
	return buffer.String()
}

func (this *While) IsEqual(otherEx Ex, es *EvalState) string {
	return "EQUAL_UNK"
}

func (this *While) IsSameQ(otherEx Ex, es *EvalState) bool {
	return false
}

func (this *While) IsMatchQ(otherEx Ex, es *EvalState) bool {
	return this.IsSameQ(otherEx, es)
}

func (this *While) DeepCopy() Ex {
	return &While{
		Test: this.Test.DeepCopy(),
		Body: this.Body.DeepCopy(),
	}
}
