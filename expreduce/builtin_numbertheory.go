package expreduce

func GetNumberTheoryDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "PrimeQ",
		Usage: "`PrimeQ[n]` returns True if `n` is prime, False otherwise.",
		legacyEvalFn: singleParamQEval(primeQ),
		SimpleExamples: []TestInstruction{
			&SameTest{"True", "PrimeQ[5]"},
			&SameTest{"False", "PrimeQ[100]"},
			&SameTest{"True", "PrimeQ[982451653]"},
			&SameTest{"True", "PrimeQ[-2]"},
		},
		FurtherExamples: []TestInstruction{
			&TestComment{"`PrimeQ` only works for Integers:"},
			&SameTest{"False", "PrimeQ[5.]"},
		},
		Tests: []TestInstruction{
			&SameTest{"False", "PrimeQ[0]"},
			&SameTest{"False", "PrimeQ[1]"},
			&SameTest{"False", "PrimeQ[-1]"},
			&SameTest{"False", "PrimeQ[0.5]"},
		},
	})
	return
}
