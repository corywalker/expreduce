package expreduce

func GetExpressionDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name:  "Apply",
		Usage: "`Apply[f, e]` (`f@@e`) replaces the head of expression `e` with `f`.",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}

			sym, isSym := this.Parts[1].(*Symbol)
			expr, isExpr := this.Parts[2].DeepCopy().(*Expression)
			if isSym && isExpr {
				toReturn := &Expression{[]Ex{sym}}
				toReturn.Parts = append(toReturn.Parts, expr.Parts[1:]...)
				return toReturn.Eval(es)
			}
			return this.Parts[2]
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"bar[syma, symb]", "Apply[bar, foo[syma, symb]]"},
			&SameTest{"bar[syma, symb]", "bar@@foo[syma, symb]"},
			&SameTest{"{syma, symb}", "List@@(syma + symb)"},
			&TestComment{"`Apply` is useful in performing aggregations on `List`s:"},
			&SameTest{"12", "Times @@ {2, 6}"},
			&SameTest{"a b", "Times @@ {a, b}"},
		},
		FurtherExamples: []TestInstruction{
			&TestComment{"`Apply` has no effect on atoms:"},
			&SameTest{"1", "foo @@ 1"},
			&SameTest{"bar", "foo @@ bar"},
		},
		Tests: []TestInstruction{
			&SameTest{"foo[a,b,c]", "Apply[foo, {a,b,c}]"},
			&SameTest{"foo[bar, buzz]", "Apply[foo, {bar, buzz}]"},
			&SameTest{"foo[bar, buzz]", "foo @@ {bar, buzz}"},
			&SameTest{"foo[1, 2]", "foo @@ {1, 2}"},
		},
	})
	defs = append(defs, Definition{
		Name:  "Sequence",
		Usage: "`Sequence[e1, e2, ...]` holds a list of expressions to be automatically inserted into another function.",
		SimpleExamples: []TestInstruction{
			&TestComment{"Sequence arguments are automatically inserted into the parent functions:"},
			&SameTest{"foo[a, 2, 3]", "foo[a, Sequence[2, 3]]"},
			&TestComment{"Outside of the context of functions, Sequence objects do not merge:"},
			&SameTest{"Sequence[2, 3]", "Sequence[2, 3]"},
			&SameTest{"14", "Sequence[2, 3] + Sequence[5, 4]"},
			&SameTest{"120", "Sequence[2, 3]*Sequence[5, 4]"},
		},
		FurtherExamples: []TestInstruction{
			&TestComment{"Empty `Sequence[]` objects effectively disappear:"},
			&SameTest{"foo[]", "foo[Sequence[]]"},
		},
		Tests: []TestInstruction{
			&SameTest{"Sequence[2]", "Sequence[2]"},
			&SameTest{"Sequence[2, 3]", "Sequence[2, 3]"},
			&SameTest{"foo[2, 3]", "foo[Sequence[2, 3]]"},
			&SameTest{"foo[2]", "foo[Sequence[2]]"},
			&SameTest{"foo[14]", "foo[Sequence[2, 3] + Sequence[5, 4]]"},
			&SameTest{"foo[2, 3, 5, 4]", "foo[Sequence[2, 3], Sequence[5, 4]]"},
			// The following tests will fail until Equal and SameQ can handle
			// multiple inputs:
			//&SameTest{"False", "Sequence[2, 3] == Sequence[2, 3]"},
			//&SameTest{"True", "Sequence[2, 2] == Sequence[2]"},
			//&SameTest{"False", "Sequence[2, 3] === Sequence[2, 3]"},
			//&SameTest{"True", "Sequence[2, 2] === Sequence[2]"},
		},
	})
	defs = append(defs, Definition{
		Name:  "Evaluate",
		Usage: "`Evaluate[expr]` evaluates to an evaluated form of `expr`, even when under hold conditions.",
		SimpleExamples: []TestInstruction{
			&StringTest{"Hold[4, (2 + 1)]", "Hold[Evaluate[1 + 3], 2 + 1]"},
			&StringTest{"Hold[foo[Evaluate[(1 + 1)]]]", "Hold[foo[Evaluate[1 + 1]]]"},
			&StringTest{"Hold[4, 7, (2 + 1)]", "Hold[Evaluate[1 + 3, 5 + 2], 2 + 1]"},
			&StringTest{"Hold[(1 + 3), (5 + 2), (2 + 1)]", "Hold[Sequence[1 + 3, 5 + 2], 2 + 1]"},
		},
	})
	defs = append(defs, Definition{
		Name: "Function",
		Usage: "`Function[inner]` defines a pure function where `inner` is evaluated with `Slot` parameters.\n\n" +
			"`Function[x, inner]` defines a pure function where `inner` is evaluated a single parameter `x`.",
		Attributes: []string{"HoldAll"},
		SimpleExamples: []TestInstruction{
			&SameTest{"1 + x", "Function[1 + #][x]"},
			&SameTest{"1 + x + 2y", "Function[1 + # + 2#2][x, y]"},
			&SameTest{"a^2", "Function[x, x^2][a]"},
			&SameTest{"a^2", "Function[x, x^2][a, b]"},
			&SameTest{"x^2", "Function[x, x^2][x]"},
			&SameTest{"4", "Function[x, x^2][-2]"},
		},
	})
	defs = append(defs, Definition{
		Name: "Slot",
		Usage: "`#` serves as a pure function's first parameter.\n\n" +
			"`#n` serves as a pure function's `n`'th parameter.",
		Attributes: []string{"NHoldAll"},
		SimpleExamples: []TestInstruction{
			&SameTest{"1 + x", "Function[1 + #][x]"},
			&SameTest{"1 + x + 2y", "Function[1 + # + 2#2][x, y]"},
			&SameTest{"True", "# === Slot[1]"},
			&SameTest{"True", "#2 === Slot[2]"},
		},
	})
	defs = append(defs, Definition{
		Name:       "Hold",
		Usage:      "`Hold[expr]` prevents automatic evaluation of `expr`.",
		Attributes: []string{"HoldAll"},
		SimpleExamples: []TestInstruction{
			&StringTest{"Hold[5^3]", "Hold[Power[5, 3]]"},
			&StringTest{"Hold[5.^3.]", "Hold[Power[5., 3.]]"},
		},
	})
	return
}
