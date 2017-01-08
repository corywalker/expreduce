package expreduce

func GetFlowControlDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "If",
		Attributes: []string{"HoldRest"},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 4 {
				return this
			}

			var isequal string = this.Parts[1].IsEqual(&Symbol{"True"}, &es.CASLogger)
			if isequal == "EQUAL_UNK" {
				return this
			} else if isequal == "EQUAL_TRUE" {
				return this.Parts[2]
			} else if isequal == "EQUAL_FALSE" {
				return this.Parts[3]
			}

			return &Expression{[]Ex{&Symbol{"Error"}, &String{"Unexpected equality return value."}}}
		},
		Tests: []TestInstruction{
			&StringTest{"True", "t=True"},
			&StringTest{"True", "t"},
			&StringTest{"False", "f=False"},
			&StringTest{"False", "f"},

			// Basic functionality
			&StringTest{"True", "If[t, True, False]"},
			&StringTest{"False", "If[f, True, False]"},
			&StringTest{"False", "If[t, False, True]"},
			&StringTest{"True", "If[f, False, True]"},

			// Test evaluation
			&StringTest{"9", "x=9"},
			&StringTest{"18", "If[x+3==12, x*2, x+3]"},
			&StringTest{"12", "If[x+3==11, x*2, x+3]"},

			// Test replacement
			&SameTest{"itsfalse", "If[1 == 2, itstrue, itsfalse]"},
			&SameTest{"itsfalse", "If[1 == 2, itstrue, itsfalse] /. (2 -> 1)"},
			&SameTest{"itstrue", "If[1 == k, itstrue, itsfalse] /. (k -> 1)"},
			&SameTest{"If[1 == k, itstrue, itsfalse]", "If[1 == k, itstrue, itsfalse]"},
		},
	})
	defs = append(defs, Definition{
		Name: "While",
		Attributes: []string{"HoldAll"},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}
			isequal := this.Parts[1].IsEqual(&Symbol{"True"}, &es.CASLogger)
			cont := isequal == "EQUAL_TRUE"
			for cont {

				isequal = this.Parts[1].IsEqual(&Symbol{"True"}, &es.CASLogger)
				cont = isequal == "EQUAL_TRUE"
			}

			if isequal == "EQUAL_UNK" {
				return &Expression{[]Ex{&Symbol{"Error"}, &String{"Encountered EQUAL_UNK when evaluating test for the While."}}}
			} else if isequal == "EQUAL_TRUE" {
				return &Symbol{"Null"}
			} else if isequal == "EQUAL_FALSE" {
				return &Symbol{"Null"}
			}

			return &Expression{[]Ex{&Symbol{"Error"}, &String{"Unexpected equality return value."}}}
		},
	})
	defs = append(defs, Definition{
		Name: "KroneckerDelta",
		Attributes: []string{"NumericFunction", "Orderless", "ReadProtected"},
		Rules: []Rule{
			{"KroneckerDelta[x_Integer]", "If[x == 0, 1, 0]"},
		},
	})
	return
}
