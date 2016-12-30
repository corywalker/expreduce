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

func ReplacePD(this Ex, cl *CASLogger, pm *PDManager) Ex {
	cl.Infof("In ReplacePD(%v, pm=%v)", this, pm)
	toReturn := this.DeepCopy()
	for nameStr, def := range pm.patternDefined {
		toReturn = ReplaceAll(toReturn,
			&Expression{[]Ex{
				&Symbol{"Rule"},
				&Symbol{nameStr},
				def,
			}}, cl, EmptyPD())
	}
	cl.Infof("Finished ReplacePD with toReturn=%v", toReturn)
	return toReturn
}

// The goal of this function is to replace all matching expressions with the
// RHS upon successful matches. We will NOT substitute any named patterns in
// the RHS. We will merely make sure that the named patterns are added to pm.
// Final named pattern substitution will occur at the last possible time.
func ReplaceAll(this Ex, r *Expression, cl *CASLogger, pm *PDManager) Ex {
	_, isFlt := this.(*Flt)
	_, isInteger := this.(*Integer)
	_, isString := this.(*String)
	asExpression, isExpression := this.(*Expression)
	_, isSymbol := this.(*Symbol)
	_, isRational := this.(*Rational)

	if isFlt || isInteger || isString || isSymbol || isRational {
		if res, matches := IsMatchQ(this, r.Parts[1], pm, cl); res {
			return ReplacePD(r.Parts[2], cl, matches)
		}
		return this
	} else if isExpression {
		cl.Debugf("ReplaceAll(%v, %v, es, %v)", this, r, pm)
		return asExpression.ReplaceAll(r, cl)
	}
	return &Symbol{"ReplaceAllFailed"}
}

func (this *Expression) ToStringReplaceAll() string {
	var buffer bytes.Buffer
	buffer.WriteString("(")
	buffer.WriteString(this.Parts[1].String())
	buffer.WriteString(") /. (")
	buffer.WriteString(this.Parts[2].String())
	buffer.WriteString(")")
	return buffer.String()
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

func GetReplacementDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		name: "ReplaceAll",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
	if len(this.Parts) != 3 {
		return this
	}

	rulesRule, ok := HeadAssertion(this.Parts[2], "Rule")
	if !ok {
		rulesRule, ok = HeadAssertion(this.Parts[2], "RuleDelayed")
	}
	if ok {
		newEx := ReplaceAll(this.Parts[1], rulesRule, &es.CASLogger, EmptyPD())
		return newEx.Eval(es)
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
				toReturn = ReplaceAll(toReturn.DeepCopy(), rulesRule, &es.CASLogger, EmptyPD())
			}
		}
		return toReturn.Eval(es)
	}

	return this
		},
	})
	defs = append(defs, Definition{
		name: "ReplaceRepeated",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
	if len(this.Parts) != 3 {
		return this
	}
	es.Infof("Starting ReplaceRepeated.")
	isSame := false
	oldEx := this.Parts[1]
	es.Infof("In ReplaceRepeated. Initial expr: %v", oldEx)
	for !isSame {
		newEx := (&Expression{[]Ex{
			&Symbol{"ReplaceAll"},
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
		},
	})
	return
}
