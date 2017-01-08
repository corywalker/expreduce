package expreduce

func GetStringDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		name: "ToString",
		rules: []Rule{
			{"ToString[a_]", "ToString[a, OutputForm]"},
		},
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
			if formAsSymbol.Name != "InputForm" && formAsSymbol.Name != "OutputForm" && formAsSymbol.Name != "FullForm" {
				return this
			}

			return &String{this.Parts[1].StringForm(formAsSymbol.Name)}
		},
	})
	defs = append(defs, Definition{
		name: "StringJoin",
		attributes: []string{"Flat", "OneIdentity"},
		rules: []Rule{
			// For some reason this is fast for StringJoin[Table["x", {k,2000}]/.List->Sequence]
			// but slow for StringJoin[Table["x", {k,2000}]]
			//"StringJoin[{args___}]": "StringJoin[args]",
			// This rule runs much faster, probably because it avoids
			// OrderlessIsMatchQ
			{"StringJoin[list_List]", "StringJoin[list /. List->Sequence]"},
		},
		toString: func(this *Expression, form string) (bool, string) {
			return ToStringInfix(this.Parts[1:], " <> ", form)
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
	return
}
