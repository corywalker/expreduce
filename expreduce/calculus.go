package expreduce

func GetCalculusDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name:       "D",
		Attributes: []string{"ReadProtected"},
		Rules: []Rule{
			{"D[x_,x_]", "1"},
			{"D[a_,x_]", "0"},
			{"D[a_+b__,x_]", "D[a,x]+D[Plus[b],x]"},
			{"D[a_ b__,x_]", "D[a,x] b+a D[Times[b],x]"},
			// The times operator is needed here. Whitespace precedence is messed up
			{"D[a_^(b_), x_]", "a^b*(D[b,x] Log[a]+D[a,x]/a*b)"},
			{"D[Log[a_], x_]", "D[a, x]/a"},
			{"D[Sin[a_], x_]", "D[a,x] Cos[a]"},
			{"D[Cos[a_], x_]", "-D[a,x] Sin[a]"},
		},
		Tests: []TestInstruction{
			&SameTest{"1", "D[x,x]"},
			&SameTest{"1", "D[foo,foo]"},
			&SameTest{"0", "D[foo,bar]"},
			&SameTest{"2", "D[bar+foo+bar,bar]"},
			&SameTest{"2x", "D[x^2,x]"},
			&SameTest{"2x+3x^2", "D[x^2+x^3,x]"},
			&SameTest{"-4x^3", "D[-x^4,x]"},
			&SameTest{"-n x^(-1 - n) + n x^(-1 + n)", "D[x^n+x^(-n),x]"},
			&SameTest{"4 x (1 + x^2)", "D[(x^2 + 1)^2, x]"},
			&SameTest{"((1 + x + (1/6 * x^3) + (1/2 * x^2)))", "D[1 + x + 1/2*x^2 + 1/6*x^3 + 1/24*x^4, x]"},
			&SameTest{"-10*Power[x,-3] - 7*Power[x,-2]", "D[1 + 7/x + 5/(x^2), x]"},
			&SameTest{"Sqrt[x] + x^(3/2)", "D[2/3*x^(3/2) + 2/5*x^(5/2), x]"},

			&SameTest{"-2 Sin[2 x]", "D[Cos[2 x], x]"},
			&SameTest{"Cos[x]/x - Sin[x]*Power[x,-2]", "D[(Sin[x]*x^-1), x]"},
			&SameTest{"-((2 Cos[x])*Power[x,-2]) + (2 Sin[x])*Power[x,-3] - Sin[x]/x", "D[D[(Sin[x]*x^-1), x], x]"},
			&SameTest{"-((2 Cos[x])*Power[x,-2]) + (2 Sin[x])*Power[x,-3] - Sin[x]/x", "D[D[(Sin[x]*x^-1+Sin[y]), x], x]"},
			&SameTest{"2/x", "D[Log[5 x^2], x]"},
			&SameTest{"-(Sin[Log[x]]/x)", "D[Cos[Log[x]], x]"},
		},
	})
	defs = append(defs, Definition{
		Name:       "Integrate",
		Attributes: []string{"ReadProtected"},
		Rules: []Rule{
			// Might need to be implemented in code. Try running Integrate[-10x, {x, 1, 5}]
			// with this
			//"Integrate[a_,{x_Symbol,start_Integer,end_Integer}]": "ReplaceAll[Integrate[a, x],x->end] - ReplaceAll[Integrate[a, x],x->start]",
			{"Integrate[a_Integer,x_Symbol]", "a*x"},
			{"Integrate[a_Integer*b_,x_Symbol]", "a*Integrate[b,x]"},
			{"Integrate[a_+b__,x_Symbol]", "Integrate[a,x]+Integrate[Plus[b],x]"},
			{"Integrate[x_Symbol^n_Integer, x_Symbol]", "x^(n+1)/(n+1)"},
			{"Integrate[x_Symbol^n_Rational, x_Symbol]", "x^(n+1)/(n+1)"},
		},
	})
	return
}
