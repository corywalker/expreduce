package cas

import "bytes"

func (this *Expression) ToStringRule() string {
	var buffer bytes.Buffer
	buffer.WriteString("(")
	buffer.WriteString(this.Parts[1].String())
	buffer.WriteString(") -> (")
	buffer.WriteString(this.Parts[2].String())
	buffer.WriteString(")")
	return buffer.String()
}

func (this *Expression) ToStringRuleDelayed() string {
	var buffer bytes.Buffer
	buffer.WriteString("(")
	buffer.WriteString(this.Parts[1].String())
	buffer.WriteString(") :> (")
	buffer.WriteString(this.Parts[2].String())
	buffer.WriteString(")")
	return buffer.String()
}

func ReplacePD(this Ex, es *EvalState) Ex {
	es.Infof("In ReplacePD(%v, es.patternDefined=%v)", this, es.patternDefined)
	toReturn := this.DeepCopy()
	for nameStr, def := range es.patternDefined {
		toReturn = Replace(toReturn,
			&Expression{[]Ex{
				&Symbol{"Rule"},
				&Symbol{nameStr},
				def,
			}}, es)
	}
	es.Infof("Finished ReplacePD with toReturn=%v", toReturn)
	return toReturn
}

func Replace(this Ex, r *Expression, es *EvalState) Ex {
	_, isFlt := this.(*Flt)
	_, isInteger := this.(*Integer)
	_, isString := this.(*String)
	asExpression, isExpression := this.(*Expression)
	_, isSymbol := this.(*Symbol)
	_, isRational := this.(*Rational)

	if isFlt || isInteger || isString || isSymbol || isRational {
		if IsMatchQ(this, r.Parts[1], es) {
			return r.Parts[2]
		}
		return this
	} else if isExpression {
		return asExpression.Replace(r, es)
	}
	return &Symbol{"ReplaceFailed"}
}

func (this *Expression) EvalReplace(es *EvalState) Ex {
	if len(this.Parts) != 3 {
		return this
	}

	rulesRule, ok := HeadAssertion(this.Parts[2], "Rule")
	if !ok {
		rulesRule, ok = HeadAssertion(this.Parts[2], "RuleDelayed")
	}
	if ok {
		newEx := Replace(this.Parts[1], rulesRule, es)
		es.ClearPD()
		return newEx
	}

	// Also handle a list of Rules
	asList, isList := HeadAssertion(this.Parts[2], "List")
	if isList {
		toReturn := this.Parts[1]
		for i := 1; i < len(asList.Parts); i++ {
			rulesRule, ok := HeadAssertion(asList.Parts[i], "Rule")
			if !ok {
				rulesRule, ok = HeadAssertion(asList.Parts[i], "RuleDelayed")
			}
			if ok {
				toReturn = Replace(toReturn.DeepCopy(), rulesRule, es)
				es.ClearPD()
			}
		}
		return toReturn
	}

	return this
}

func (this *Expression) ToStringReplace() string {
	var buffer bytes.Buffer
	buffer.WriteString("(")
	buffer.WriteString(this.Parts[1].String())
	buffer.WriteString(") /. (")
	buffer.WriteString(this.Parts[2].String())
	buffer.WriteString(")")
	return buffer.String()
}

func (this *Expression) EvalReplaceRepeated(es *EvalState) Ex {
	if len(this.Parts) != 3 {
		return this
	}
	es.Infof("Starting ReplaceRepeated.")
	isSame := false
	oldEx := this.Parts[1]
	es.Infof("In ReplaceRepeated. Initial expr: %v", oldEx)
	for !isSame {
		newEx := (&Expression{[]Ex{
			&Symbol{"Replace"},
			oldEx.DeepCopy(),
			this.Parts[2],
		}}).Eval(es)
		//newEx = newEx.Eval(es)
		es.Infof("In ReplaceRepeated. New expr: %v", newEx)

		if IsSameQ(oldEx, newEx, &es.CASLogger) {
			isSame = true
		}
		oldEx = newEx
	}
	return oldEx
}

func (this *Expression) ToStringReplaceRepeated() string {
	var buffer bytes.Buffer
	buffer.WriteString("(")
	buffer.WriteString(this.Parts[1].String())
	buffer.WriteString(") //. (")
	buffer.WriteString(this.Parts[2].String())
	buffer.WriteString(")")
	return buffer.String()
}
