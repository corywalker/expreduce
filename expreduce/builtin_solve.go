package expreduce

func GetSolveDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "Solve",
		// Flip parameter order because of matching bug:
		Usage: "`Solve[var, eqn]` solves `eqn` for `var`.",
		Details: "!!! warning \"Under development\"\n" +
			"	This function is under development, and as such will be incomplete and inaccurate. The function currently only knows how to solve a few example forms of equations.",
		Rules: []Rule{
			{"Solve[x_, x_ == expr_]", "{{x -> expr}}"},
			{"Solve[x_, x_ * exprB__ == exprA_]", "{{x -> exprA / Times[exprB]}}"},
			{"Solve[x_, x_ * exprB__ + exprC_ == exprA_]", "{{x -> (exprA-exprC) / Times[exprB]}}"},
			{"Solve[x_, a_*x_^2 + b_*x_ + c_ == d_]", "{{x -> (-b - Sqrt[b^2 - 4 a c + 4 a d])/(2 a)}, {x -> (-b + Sqrt[b^2 - 4 a c + 4 a d])/(2 a)}}"},
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"{{x -> 0}}", "Solve[x, x == 0]"},
			&SameTest{"{{x -> b}}", "Solve[x, x == b]"},
			&SameTest{"{{x -> a b}}", "Solve[x, x/a == b]"},
			&SameTest{"{{x -> b/a}}", "Solve[x, x*a == b]"},
			&SameTest{"{{x -> -(b/m)}}", "Solve[x, m*x + b == 0]"},
			&SameTest{"{{x -> (-b + c)/m}}", "Solve[x, m*x + b == c]"},
			&SameTest{"{{x -> (-b - Sqrt[b^2 - 4 a c])/(2 a)}, {x -> (-b + Sqrt[b^2 - 4 a c])/(2 a)}}", "Solve[x, a*x^2 + b*x + c == 0]"},
			&SameTest{"{{x -> (-b - Sqrt[b^2 - 4 a c + 4 a d])/(2 a)}, {x -> (-b + Sqrt[b^2 - 4 a c + 4 a d])/(2 a)}}", "Solve[x, a*x^2 + b*x + c == d]"},
		},
	})
	return
}
