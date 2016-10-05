package cas

func (this *Expression) EvalIf(es *EvalState) Ex {
	if len(this.Parts) != 4 {
		return this
	}

	var isequal string = this.Parts[1].Eval(es).IsEqual(&Symbol{"True"}, es)
	if isequal == "EQUAL_UNK" {
		return this
	} else if isequal == "EQUAL_TRUE" {
		return this.Parts[2].Eval(es)
	} else if isequal == "EQUAL_FALSE" {
		return this.Parts[3].Eval(es)
	}

	return &Error{"Unexpected equality return value."}
}

func (this *Expression) EvalWhile(es *EvalState) Ex {
	if len(this.Parts) != 3 {
		return this
	}
	isequal := this.Parts[1].Eval(es).IsEqual(&Symbol{"True"}, es)
	cont := isequal == "EQUAL_TRUE"
	for cont {

		isequal = this.Parts[1].Eval(es).IsEqual(&Symbol{"True"}, es)
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
