package expreduce

func GetFlowControlDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name:       "If",
		Usage:      "`If[cond, iftrue, iffalse]` returns `iftrue` if `cond` is True, and `iffalse` if `cond` is False.",
		Attributes: []string{"HoldRest"},
		// WARNING: Watch out for putting rules here. It can interfere with how
		// Return works.
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) > 4 || len(this.Parts) < 3 {
				return this
			}
			var falseVal Ex = &Symbol{"Null"}
			if len(this.Parts) == 4 {
				falseVal = this.Parts[3]
			}

			var isequal string = this.Parts[1].IsEqual(&Symbol{"True"}, &es.CASLogger)
			if isequal == "EQUAL_UNK" {
				return this
			} else if isequal == "EQUAL_TRUE" {
				return this.Parts[2]
			} else if isequal == "EQUAL_FALSE" {
				return falseVal
			}

			return NewExpression([]Ex{&Symbol{"Error"}, &String{"Unexpected equality return value."}})
		},
		SimpleExamples: []TestInstruction{
			&StringTest{"9", "x=9"},
			&StringTest{"18", "If[x+3==12, x*2, x+3]"},
			&StringTest{"12", "If[x+3==11, x*2, x+3]"},
		},
		FurtherExamples: []TestInstruction{
			&TestComment{"Undefined conditions leave the statement unevaluated."},
			&StringTest{"If[undefined, a, b]", "If[undefined, a, b]"},
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

			// Test replacement
			&SameTest{"itsfalse", "If[1 == 2, itstrue, itsfalse]"},
			&SameTest{"itsfalse", "If[1 == 2, itstrue, itsfalse] /. (2 -> 1)"},
			&SameTest{"itstrue", "If[1 == k, itstrue, itsfalse] /. (k -> 1)"},
			&SameTest{"If[1 == k, itstrue, itsfalse]", "If[1 == k, itstrue, itsfalse]"},
			&SameTest{"a", "If[True, a]"},
			&SameTest{"Null", "If[False, a]"},
		},
	})
	defs = append(defs, Definition{
		Name:       "While",
		Usage:      "`While[cond, body]` evaluates `cond`, and if it returns True, evaluates `body`. This happens repeatedly.",
		Attributes: []string{"HoldAll"},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}
			isequal := this.Parts[1].Eval(es).IsEqual(&Symbol{"True"}, &es.CASLogger)
			cont := isequal == "EQUAL_TRUE"
			for cont {
				tmpRes := this.Parts[2].Eval(es)
				retVal, isReturn := tryReturnValue(tmpRes)
				if isReturn {
					return retVal
				}
				isequal = this.Parts[1].Eval(es).IsEqual(&Symbol{"True"}, &es.CASLogger)
				cont = isequal == "EQUAL_TRUE"
			}

			if isequal == "EQUAL_UNK" {
				return NewExpression([]Ex{&Symbol{"Error"}, &String{"Encountered EQUAL_UNK when evaluating test for the While."}})
			} else if isequal == "EQUAL_TRUE" {
				return &Symbol{"Null"}
			} else if isequal == "EQUAL_FALSE" {
				return &Symbol{"Null"}
			}

			return NewExpression([]Ex{&Symbol{"Error"}, &String{"Unexpected equality return value."}})
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"1", "a=1"},
			&SameTest{"Null", "While[a != 5, a = a + 1]"},
			&SameTest{"5", "a"},
		},
	})
	defs = append(defs, Definition{
		Name:       "CompoundExpression",
		Usage:      "`CompoundExpression[e1, e2, ...]` evaluates each expression in order and returns the result of the last one.",
		Attributes: []string{"HoldAll", "ReadProtected"},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			var toReturn Ex
			for i := 1; i < len(this.Parts); i++ {
				toReturn = this.Parts[i].Eval(es)
				if _, isReturn := HeadAssertion(toReturn, "Return"); isReturn {
					return toReturn
				}
			}
			return toReturn
		},
		SimpleExamples: []TestInstruction{
			&TestComment{"The result of the first expression is not included in the output, but the result of the second is:"},
			&SameTest{"3", "a = 5; a - 2"},
			&TestComment{"Including a trailing semicolon causes the expression to return `Null`:"},
			&SameTest{"Null", "a = 5; a - 2;"},
		},
	})
	// https://mathematica.stackexchange.com/questions/29353/how-does-return-work
	defs = append(defs, Definition{
		Name:  "Return",
		Usage: "`Return[x]` returns `x` immediately.",
		SimpleExamples: []TestInstruction{
			&SameTest{"x", "myreturnfunc:=(Return[x];hello);myreturnfunc"},
			&SameTest{"3", "ret[x_]:=(Return[x];hello);ret[3]"},
			&SameTest{"3", "myfoo:=(i=1;While[i<5,If[i===3,Return[i]];i=i+1]);myfoo"},
			&SameTest{"Return[3]", "Return[3]"},
			&SameTest{"Null", "retother:=(Return[];hello);retother"},
		},
	})
	return
}
