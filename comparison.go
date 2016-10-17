package cas

import "bytes"

func (this *Expression) EvalEqual(es *EvalState) Ex {
	if len(this.Parts) != 3 {
		return this
	}

	var isequal string = this.Parts[1].Eval(es).IsEqual(this.Parts[2].Eval(es), es)
	if isequal == "EQUAL_UNK" {
		return this
	} else if isequal == "EQUAL_TRUE" {
		return &Symbol{"True"}
	} else if isequal == "EQUAL_FALSE" {
		return &Symbol{"False"}
	}

	return &Expression{[]Ex{&Symbol{"Error"}, &String{"Unexpected equality return value."}}}
}

func (this *Expression) ToStringEqual() string {
	var buffer bytes.Buffer
	buffer.WriteString("(")
	buffer.WriteString(this.Parts[1].String())
	buffer.WriteString(") == (")
	buffer.WriteString(this.Parts[2].String())
	buffer.WriteString(")")
	return buffer.String()
}

func (this *Expression) EvalSameQ(es *EvalState) Ex {
	if len(this.Parts) != 3 {
		return this
	}

	var issame bool = IsSameQ(this.Parts[1].Eval(es), this.Parts[2].Eval(es), es)
	if issame {
		return &Symbol{"True"}
	} else {
		return &Symbol{"False"}
	}
}

func (this *Expression) ToStringSameQ() string {
	var buffer bytes.Buffer
	buffer.WriteString("(")
	buffer.WriteString(this.Parts[1].String())
	buffer.WriteString(") === (")
	buffer.WriteString(this.Parts[2].String())
	buffer.WriteString(")")
	return buffer.String()
}

func IsMatchQ(a Ex, b Ex, es *EvalState) bool {
	_, aIsFlt := a.(*Flt)
	_, aIsInteger := a.(*Integer)
	_, aIsString := a.(*String)
	aExpression, aIsExpression := a.(*Expression)
	_, aIsSymbol := a.(*Symbol)

	// This initial value is just a randomly chosen placeholder
	headStr := "Unknown"
	if aIsFlt {
		headStr = "Real"
	} else if aIsInteger {
		headStr = "Integer"
	} else if aIsString {
		headStr = "String"
	} else if aIsExpression {
		headStr = aExpression.Parts[0].String()
	} else if aIsSymbol {
		headStr = "Symbol"
	}

	if IsBlankTypeCapturing(b, a, headStr, es) {
		return true
	}
	if aIsFlt || aIsInteger || aIsString || aIsSymbol {
		return IsSameQ(a, b, es)
	}
	return aExpression.IsMatchQ(b, es)
}

func IsSameQ(a Ex, b Ex, es *EvalState) bool {
	isSame := false
	_, aIsFlt := a.(*Flt)
	_, bIsFlt := b.(*Flt)
	_, aIsInteger := a.(*Integer)
	_, bIsInteger := b.(*Integer)
	_, aIsString := a.(*String)
	_, bIsString := b.(*String)
	aExpression, aIsExpression := a.(*Expression)
	_, aIsSymbol := a.(*Symbol)
	_, bIsSymbol := b.(*Symbol)

	if (aIsFlt && bIsFlt) || (aIsString && bIsString) || (aIsInteger && bIsInteger) || (aIsSymbol && bIsSymbol) {
		isSame = a.IsEqual(b, es) == "EQUAL_TRUE"
	} else if aIsExpression {
		isSame = aExpression.IsSameQ(b, es)
	}
	return isSame
}
func IsMatchQClearDefs(a Ex, b Ex, es *EvalState) bool {
	oldVars := es.GetDefinedSnapshot()
	isSame := IsMatchQ(a, b, es)
	es.ClearPD()
	es.defined = oldVars
	return isSame
}

func (this *Expression) EvalMatchQ(es *EvalState) Ex {
	if len(this.Parts) != 3 {
		return this
	}

	if IsMatchQClearDefs(this.Parts[1], this.Parts[2], es) {
		return &Symbol{"True"}
	} else {
		return &Symbol{"False"}
	}
}
