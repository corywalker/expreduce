package expreduce

func getSpecialSymsDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name:       "Infinity",
		Usage:      "`Infinity` represents the mathematical concept of infinity.",
		Attributes: []string{"ReadProtected"},
		Rules: []Rule{
			{"Plus[Infinity, _Integer, rest___]", "Infinity + rest"},
			{"Plus[Infinity, _Real, rest___]", "Infinity + rest"},
			{"Plus[-Infinity, _Integer, rest___]", "-Infinity + rest"},
			{"Plus[-Infinity, _Real, rest___]", "-Infinity + rest"},
			{"Plus[Infinity, -Infinity, rest___]", "Indeterminate + rest"},
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"Infinity", "Infinity - 1"},
			&SameTest{"Infinity", "Infinity - 990999999"},
			&SameTest{"Infinity", "Infinity - 990999999."},
			&SameTest{"Indeterminate", "Infinity - Infinity"},
			// I can't simplify this type of infinity until I have ;/ rules
			//&SameTest{"Infinity", "Infinity*2"},
			&SameTest{"-Infinity", "Infinity*-1"},
			&SameTest{"-Infinity", "-Infinity + 1"},
			&SameTest{"-Infinity", "-Infinity + 999"},
			&SameTest{"Infinity", "-Infinity*-1"},
			&SameTest{"0", "1/Infinity"},
		},
	})
	defs = append(defs, Definition{
		Name:  "ComplexInfinity",
		Usage: "`ComplexInfinity` represents an an infinite quantity that extends in an unknown direction in the complex plane.",
		SimpleExamples: []TestInstruction{
			&SameTest{"ComplexInfinity", "0^(-1)"},
			&SameTest{"ComplexInfinity", "a/0"},
			&SameTest{"ComplexInfinity", "ComplexInfinity * foo[x]"},
			&SameTest{"ComplexInfinity", "Factorial[-1]"},
		},
	})
	defs = append(defs, Definition{
		Name:  "Indeterminate",
		Usage: "`Indeterminate` represents an indeterminate form.",
		SimpleExamples: []TestInstruction{
			&SameTest{"Indeterminate", "0/0"},
			&SameTest{"Indeterminate", "Infinity - Infinity"},
			&SameTest{"Indeterminate", "0 * Infinity"},
			&SameTest{"Indeterminate", "0 * ComplexInfinity"},
			&SameTest{"Indeterminate", "0^0"},
		},
	})
	defs = append(defs, Definition{
		Name:       "Pi",
		Usage:      "`Pi` is the constant of pi.",
		Attributes: []string{"ReadProtected", "Constant"},
		Rules: []Rule{
			{"N[Pi]", "3.141592653589793238462643383279502884197"},
			{"Times[Pi, a_Real, rest___]", "N[Pi] * a * rest"},
		},
	})
	defs = append(defs, Definition{
		Name:       "E",
		Usage:      "`E` is the constant for the base of the natural logarithm.",
		Attributes: []string{"ReadProtected", "Constant"},
		Rules: []Rule{
			{"N[E]", "2.71828182845904523536028747135266249775724709370"},
			{"Times[E, a_Real, rest___]", "N[E] * a * rest"},
		},
	})
	return
}
