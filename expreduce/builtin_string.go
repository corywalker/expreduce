package expreduce

func GetStringDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name:  "ToString",
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
			return &String{this.Parts[1].StringForm(formAsSymbol.Name[7:], context, contextPath)}
		},
	})
	defs = append(defs, Definition{
		Name:       "StringJoin",
		toString: func(this *Expression, form string, context *String, contextPath *Expression) (bool, string) {
			return ToStringInfix(this.Parts[1:], " <> ", form, context, contextPath)
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
			return &String{toReturn}
		},
	})
	defs = append(defs, Definition{
		Name:     "Infix",
		toString: (*Expression).ToStringInfix,
	})
	return
}
