package expreduce

func GetStringDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name:  "ToString",
		Usage: "`ToString[expr, form]` converts `expr` into a string using printing method `form`.",
		Rules: []Rule{
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
			if formAsSymbol.Name != "System`InputForm" && formAsSymbol.Name != "System`OutputForm" && formAsSymbol.Name != "System`FullForm" {
				return this
			}

			return &String{this.Parts[1].StringForm(formAsSymbol.Name[7:])}
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"\"a^2\"", "ToString[a^2, InputForm]"},
			&SameTest{"\"Hello World\"", "\"Hello World\" // ToString"},
		},
	})
	defs = append(defs, Definition{
		Name:       "StringJoin",
		Usage:      "`s1 <> s2 <> ...` can join a list of strings into a single string.",
		Attributes: []string{"Flat", "OneIdentity"},
		Rules: []Rule{
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
		SimpleExamples: []TestInstruction{
			&SameTest{"\"Hello World\"", "\"Hello\" <> \" \" <> \"World\""},
			&SameTest{"\"If a=2, then a^2=4\"", "\"If a=2, then \" <> ToString[a^2, InputForm] <> \"=\" <> ToString[a^2 /. a -> 2, InputForm]"},
		},
		FurtherExamples: []TestInstruction{
			&TestComment{"The `StringJoin` of nothing is the empty string:"},
			&SameTest{"\"\"", "StringJoin[]"},
			&TestComment{"If `StringJoin` receives any non-string arguments, the expression does not evaluate:"},
			&SameTest{"\"Hello\" <> 5", "StringJoin[\"Hello\", 5]"},
			&TestComment{"This function takes `List` arguments as well:"},
			&SameTest{"\"abc\"", "StringJoin[{\"a\", \"b\", \"c\"}]"},
		},
	})
	defs = append(defs, Definition{
		Name:     "Infix",
		Usage:    "`Infix[expr, sep]` represents `expr` in infix form with separator `sep` when converted to a string.",
		toString: (*Expression).ToStringInfix,
		SimpleExamples: []TestInstruction{
			&SameTest{"\"(bar|fuzz|zip)\"", "Infix[foo[bar, fuzz, zip], \"|\"] // ToString"},
		},
	})
	return
}
