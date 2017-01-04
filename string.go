package cas

func GetString(ex Ex, form string, es *EvalState) string {
	str, isStr := ((&Expression{[]Ex{
		&Symbol{"ToString"},
		ex,
		&Symbol{form},
	}}).Eval(es)).(*String)
	if isStr {
		return str.Val
	}
	return "ERROR: RESULT WAS NOT STRING!"
}

func GetStringDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		name: "ToString",
		rules: map[string]string{
			"ToString[amatch_]": "ToString[amatch, OutputForm]",
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
			if formAsSymbol.Name != "InputForm" && formAsSymbol.Name != "OutputForm" {
				return this
			}

			exAsExpr, exIsExpr := this.Parts[1].(*Expression)
			var toStringify Ex
			if exIsExpr {
				toStringify = exAsExpr.Format(es, formAsSymbol.Name, true)
			} else {
				toStringify = this.Parts[1]
			}
			return &String{toStringify.StringForm(formAsSymbol.Name)}
		},
	})
	defs = append(defs, Definition{
		name: "StringJoin",
		rules: map[string]string{
			"Format[StringJoin[args___], InputForm|OutputForm]": "Infix[{args}, \" <> \"]",
			// For some reason this is fast for StringJoin[Table["x", {k,2000}]/.List->Sequence]
			// but slow for StringJoin[Table["x", {k,2000}]]
			//"StringJoin[{args___}]": "StringJoin[args]",
			// This rule runs much faster, probably because it avoids
			// CommutativeIsMatchQ
			"StringJoin[listmatch_List]": "StringJoin[listmatch /. List->Sequence]",
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
