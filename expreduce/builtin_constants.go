package expreduce

func getConstantsDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name:  "Rational",
		Usage: "`Rational` is the head for the atomic rational type.",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}
			nAsInt, nIsInt := this.Parts[1].(*Integer)
			dAsInt, dIsInt := this.Parts[2].(*Integer)
			if nIsInt && dIsInt {
				return (&Rational{nAsInt.Val, dAsInt.Val}).Eval(es)
			}
			return this
		},
		SimpleExamples: []TestInstruction{
			&TestComment{"Rationals are created from `Times` when a rational form is encountered:"},
			&SameTest{"Rational", "Times[5, 6^-1] // Head"},
			&TestComment{"Which is equivalent to typing them in directly:"},
			&SameTest{"Rational", "5/6 // Head"},
			&TestComment{"Or being even more explicit:"},
			&SameTest{"Rational", "Rational[5, 6] // Head"},
			&TestComment{"Rationals simplify on evaluation:"},
			&StringTest{"5/3", "Rational[10, 6]"},
			&TestComment{"Which might include evaluating to an Integer:"},
			&SameTest{"Integer", "Rational[-100, 10] // Head"},
			&TestComment{"Rationals of non-Integer types are not allowed:"},
			&StringTest{"Rational[0, n]", "Rational[0, n]"},
		},
		FurtherExamples: []TestInstruction{
			&TestComment{"Undefined rationals are handled accordingly:"},
			&StringTest{"Indeterminate", "Rational[0, 0]"},
			&StringTest{"ComplexInfinity", "Rational[1, 0]"},
			&TestComment{"Rational numbers have some special handling for pattern matching:"},
			&SameTest{"2/3", "test = Rational[2, 3]"},
			&SameTest{"True", "MatchQ[test, 2/3]"},
			&SameTest{"True", "MatchQ[test, Rational[a_Integer, b_Integer]]"},
			&SameTest{"{2, 3}", "2/3 /. Rational[a_Integer, b_Integer] -> {a, b}"},
			&SameTest{"2/3", "2/3 /. a_Integer/b_Integer -> {a, b}"},
		},
		Tests: []TestInstruction{
			&StringTest{"10/7", "Rational[10, 7]"},
			&StringTest{"Rational[x, 10]", "Rational[x, 10]"},
			&StringTest{"10", "Rational[100, 10]"},
			&StringTest{"-10", "Rational[-100, 10]"},
			&StringTest{"10", "Rational[-100, -10]"},
			&StringTest{"-5/3", "Rational[-10, 6]"},
			&StringTest{"5/3", "Rational[-10, -6]"},
			&StringTest{"0", "Rational[0, 5]"},
			&StringTest{"Rational[0, n]", "Rational[0, n]"},
			&StringTest{"ComplexInfinity", "Rational[-1, 0]"},
			&StringTest{"ComplexInfinity", "Rational[-1, -0]"},
			&StringTest{"Indeterminate", "Rational[-0, -0]"},
			&StringTest{"Indeterminate", "Rational[-0, 0]"},

			// Rational matching and replacement
			&SameTest{"buzz[bar]", "foo[bar, 1/2] /. foo[base_, 1/2] -> buzz[base]"},
			&SameTest{"buzz[bar]", "foo[bar, 1/2] /. foo[base_, Rational[1, 2]] -> buzz[base]"},
			&SameTest{"buzz[bar]", "foo[bar, Rational[1, 2]] /. foo[base_, 1/2] -> buzz[base]"},
			&SameTest{"buzz[bar]", "foo[bar, Rational[1, 2]] /. foo[base_, Rational[1, 2]] -> buzz[base]"},
			&SameTest{"True", "MatchQ[1/2, Rational[1, 2]]"},
			&SameTest{"True", "MatchQ[Rational[1, 2], 1/2]"},
			&SameTest{"False", "Hold[Rational[1, 2]] === Hold[1/2]"},
		},
	})
	defs = append(defs, Definition{
		Name:  "NumberQ",
		Usage: "`NumberQ[expr]` returns True if `expr` is numeric, otherwise False.",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}
			_, ok := this.Parts[1].(*Integer)
			if ok {
				return &Symbol{"True"}
			}
			_, ok = this.Parts[1].(*Flt)
			if ok {
				return &Symbol{"True"}
			}
			_, ok = this.Parts[1].(*Rational)
			if ok {
				return &Symbol{"True"}
			}
			return &Symbol{"False"}
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"True", "NumberQ[2]"},
			&SameTest{"True", "NumberQ[2.2]"},
			&SameTest{"True", "NumberQ[Rational[5, 2]]"},
			&SameTest{"False", "NumberQ[Infinity]"},
			&SameTest{"False", "NumberQ[Sqrt[2]]"},
			&SameTest{"False", "NumberQ[randomvar]"},
			&SameTest{"False", "NumberQ[\"hello\"]"},
		},
	})
	defs = append(defs, Definition{
		Name:  "String",
		Usage: "`String` is the head for the atomic string type.",
		SimpleExamples: []TestInstruction{
			&SameTest{"\"Hello\"", "\"Hello\""},
			&SameTest{"True", "\"Hello\" == \"Hello\""},
			&SameTest{"False", "\"Hello\" == \"Hello world\""},
			&SameTest{"String", "Head[\"Hello\"]"},
		},
	})
	defs = append(defs, Definition{
		Name:  "Real",
		Usage: "`Real` is the head for the atomic floating point type.",
		SimpleExamples: []TestInstruction{
			&SameTest{"Real", "Head[1.53]"},
			&TestComment{"One can force Real interperetation on an Integer by appending a decimal point:"},
			&SameTest{"Real", "Head[1.]"},
			&TestComment{"Real numbers are backed by arbitrary-precision floating points:"},
			&StringTest{"10.", "10.^5000 / 10.^4999"},
		},
		FurtherExamples: []TestInstruction{
			&SameTest{"True", "MatchQ[1.53, _Real]"},
		},
	})
	defs = append(defs, Definition{
		Name:  "Integer",
		Usage: "`Integer` is the head for the atomic integer type.",
		SimpleExamples: []TestInstruction{
			&SameTest{"Integer", "Head[153]"},
			&TestComment{"Integer numbers are backed by arbitrary-precision data structures:"},
			&SameTest{"815915283247897734345611269596115894272000000000", "Factorial[40]"},
		},
		FurtherExamples: []TestInstruction{
			&SameTest{"True", "MatchQ[153, _Integer]"},
		},
	})
	return
}
