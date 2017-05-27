package expreduce

func GetSolveDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "Solve",
		Usage: "`Solve[eqn, var]` solves `eqn` for `var`.",
		Details: "!!! warning \"Under development\"\n" +
			"	This function is under development, and as such will be incomplete and inaccurate. The function currently only knows how to solve a few example forms of equations.",
		Rules: []Rule{
			{"Solve[x_ == expr_, x_]", "{{x -> expr}}"},
			{"Solve[x_ * exprB__ == exprA_, x_]", "{{x -> exprA / Times[exprB]}}"},
			{"Solve[x_ * exprB__ + exprC_ == exprA_, x_]", "{{x -> (exprA-exprC) / Times[exprB]}}"},
			{"Solve[a_*x_^2 + b_*x_ + c_ == d_, x_]", "{{x -> (-b - Sqrt[b^2 - 4 a c + 4 a d])/(2 a)}, {x -> (-b + Sqrt[b^2 - 4 a c + 4 a d])/(2 a)}}"},
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"{{x -> 0}}", "Solve[x == 0, x]"},
			&SameTest{"{{x -> b}}", "Solve[x == b, x]"},
			&SameTest{"{{x -> a b}}", "Solve[x/a == b, x]"},
			&SameTest{"{{x -> b/a}}", "Solve[x*a == b, x]"},
			&SameTest{"{{x -> -(b/m)}}", "Solve[m*x + b == 0, x]"},
			&SameTest{"{{x -> (-b + c)/m}}", "Solve[m*x + b == c, x]"},
			&SameTest{"{{x -> (-b - Sqrt[b^2 - 4 a c])/(2 a)}, {x -> (-b + Sqrt[b^2 - 4 a c])/(2 a)}}", "Solve[a*x^2 + b*x + c == 0, x]"},
			&SameTest{"{{x -> (-b - Sqrt[b^2 - 4 a c + 4 a d])/(2 a)}, {x -> (-b + Sqrt[b^2 - 4 a c + 4 a d])/(2 a)}}", "Solve[a*x^2 + b*x + c == d, x]"},
		},
	})
	return
}
