package expreduce

func GetStringDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "ToString",
		// For some reason this is fast for StringJoin[Table["x", {k,2000}]/.List->Sequence]
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}

			formAsSymbol, formIsSymbol := this.Parts[2].(*Symbol)
			if !formIsSymbol {
				return this
			}

			// Do not implement FullForm here. It is not officially supported
			if formAsSymbol.Name != "System`InputForm" && formAsSymbol.Name != "System`OutputForm" && formAsSymbol.Name != "System`FullForm" {
				return this
			}

			context, contextPath := ActualStringFormArgs(es)
			return NewString(this.Parts[1].StringForm(ToStringParams{form: formAsSymbol.Name[7:], context: context, contextPath: contextPath, previousHead: "<TOPLEVEL>"}))
		},
	})
	defs = append(defs, Definition{
		Name: "StringJoin",
		toString: func(this *Expression, params ToStringParams) (bool, string) {
			return ToStringInfix(this.Parts[1:], " <> ", "", params)
		},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			toReturn := ""
			for _, e := range this.Parts[1:] {
				asStr, isStr := e.(*String)
				if !isStr {
					return this
				}
				toReturn += asStr.Val
			}
			return NewString(toReturn)
		},
	})
	defs = append(defs, Definition{
		Name:     "Infix",
		toString: (*Expression).ToStringInfix,
	})
	defs = append(defs, Definition{
		Name: "StringLength",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}
			asStr, isStr := this.Parts[1].(*String)
			if !isStr {
				return this
			}
			return NewInt(int64(len(asStr.Val)))
		},
	})
	defs = append(defs, Definition{
		Name: "StringTake",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}
			asStr, isStr := this.Parts[1].(*String)
			if !isStr {
				return this
			}
			asList, isList := HeadAssertion(this.Parts[2], "System`List")
			if !isList || len(asList.Parts) != 3 {
				return this
			}
			sInt, sIsInt := asList.Parts[1].(*Integer)
			eInt, eIsInt := asList.Parts[2].(*Integer)
			if !sIsInt || !eIsInt {
				return this
			}
			s := int(sInt.Val.Int64() - 1)
			e := int(eInt.Val.Int64() - 1)
			if s < 0 || e >= len(asStr.Val) {
				return this
			}
			if e < s {
				return NewString("")
			}
			return NewString(asStr.Val[s : e+1])
		},
	})
	return
}
