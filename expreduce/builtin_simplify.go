package expreduce

func GetSimplifyDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "Simplify",
		Usage: "`Simplify[expr]` attempts to perform simplification operations on `expr`.",
		SimpleExamples: []TestInstruction{
			&TestComment{"`Simplify` can simplify some boolean expressions."},
			&SameTest{"b", "b && b // Simplify"},
			&SameTest{"False", "a && b && !b // Simplify"},
		},
		Rules: []Rule{
			{"Simplify[exp_]", "exp //. {" +
				"a_ && !a_ :> False, " +
				"!a_ && a_ :> False, " +
				"a_ && a_  :> a, " +
				"a_ || a_  :> a, " +
				"a_ || !a_ :> True, " +
				"!a_ || a_ :> True" +
			"}"},
		},
	})
	return
}
