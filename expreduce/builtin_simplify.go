package expreduce

func GetSimplifyDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "Simplify",
		Usage: "`Simplify[expr]` attempts to perform simplification operations on `expr`.",
		SimpleExamples: []TestInstruction{
			&TestComment{"`Simplify` can simplify some boolean expressions."},
			&SameTest{"b", "b && b // Simplify"},
			&SameTest{"False", "a && b && !b // Simplify"},
			&SameTest{"a || (b && c)", "(a || b) && (a || c) // Simplify"},
			&SameTest{"a || b", "a || ! a && b // Simplify"},
			&SameTest{"True", "a || b || ! a || ! b // Simplify"},
		},
		Tests: []TestInstruction{
			// Seems wrong, but this is the right behavior
			&SameTest{"a", "a || (a && Infinity) // Simplify"},

			&SameTest{"a || (b && c)", "(b || a) && (c || a) // Simplify"},

			&SameTest{"True", "(a || b || c || Not[(a && b && c)]) // Simplify"},
			&SameTest{"True", "(a || b || c || Not[(a && b && c && d)]) // Simplify"},
			&SameTest{"True", "(a || b || c || d || Not[(a && b && c)]) // Simplify"},
			&SameTest{"True", "(a || b || c || d || Not[a]) // Simplify"},
			&SameTest{"True", "(az || b || cz || Not[(ay && b && cy && dy)]) // Simplify"},

			&SameTest{"a", "a || (a && b && c && d) // Simplify"},
			&SameTest{"d", "d || (a && b && c && d) // Simplify"},
			&SameTest{"d || e", "d || e || (a && b && c && d) // Simplify"},
			&SameTest{"b || d", "d || b || (a && b && c && d) // Simplify // Sort"},
			&SameTest{"True", "d || b || (a && b && c && d) || ! b // Simplify"},
			&SameTest{"foo[True]", "foo[d || b || (a && b && c && d) || ! b] // Simplify"},
			&SameTest{"d || e || (a && b && c)", "d || e || (a && b && c) // Simplify"},
			&SameTest{"z", "z || z // Simplify"},
			&SameTest{"a || z", "z || a || z // Simplify // Sort"},
			&SameTest{"a", "a || a && b // Simplify"},
			&SameTest{"a || b", "a || !a && b // Simplify"},

			&SameTest{"a || b || c", "a || c || ! a && b // Simplify // Sort"},
			&SameTest{"a || b || c", "a || c || ! a && ! c && b // Simplify // Sort"},
			&SameTest{"a || c || !b", "a || c || ! a && ! c && ! b // Simplify // Sort"},
			&SameTest{"a || c || (! b && d)", "a || c || ! a && ! c && ! b && d // Simplify // Sort"},
			&SameTest{"a || c || Not[b]", "c || a || Not[b] // Simplify // Sort"},
		},
		Rules: []Rule{
			{"Simplify[exp_]", "exp //. {" +
				"a_ && !a_ :> False, " +
				"!a_ && a_ :> False, " +

				"a_ && a_  :> a, " +
				// "a_ || a_  :> a, " +

				"!x_ || !y_  :> !(x && y), " +
				// "a_ || (a_ && b_) :> a, " +
				// "a_ || !a_ && b_ :> a || b, " +

				"(a_ || b_) && (a_ || c_) :> a || (b && c), " +
				"(b_ || a_) && (c_ || a_) :> a || (b && c), " +

				"Or[___, a_, ___, Not[And[___, a_, ___] | a_], ___] :> True, " +
				"Or[___, Not[And[___, a_, ___] | a_], ___, a_, ___] :> True, " +
				"Or[x1___, a_, x2___, And[x3___, a_, x4___], x5___] :> a || x1 || x2 || x5, " +
				"Or[x1___, And[x2___, a_, x3___], x4___, a_, x5___] :> a || x1 || x4 || x5, " +
				"Or[x1___, a_, x2___, a_, x3___] :> a || x1 || x2 || x3, " +

				"Or[x1___, a_, x2___, And[x3___, !a_, x4___], x5___] :> a || x1 || x2 || (x3 && x4) || x5, " +
				"Or[x1___, And[x2___, !a_, x3___], x4___, a_, x5___] :> a || x1 || (x2 && x3) || x4 || x5" +
			"}"},
		},
	})
	return
}
