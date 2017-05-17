package expreduce

import "math/big"

func getFunctionalDefinitions() (defs []Definition) {
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
			&SameTest{"2a + 4b", "(4 # + (2 # &)[a] &)[b]"},
		},
		Tests: []TestInstruction{
			&SameTest{"foo[test, k]", "(foo[test, #] &) &[j][k]"},
		},
	})
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
				toReturn := NewExpression([]Ex{sym})
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
		Name:  "Map",
		Usage: "`Map[f, expr]` returns a new expression with the same head as `expr`, but with `f` mapped to each of the arguments.",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}

			expr, isExpr := this.Parts[2].(*Expression)
			if isExpr {
				toReturn := NewExpression([]Ex{expr.Parts[0]})
				for i := 1; i < len(expr.Parts); i++ {
					toReturn.Parts = append(toReturn.Parts, NewExpression([]Ex{
						this.Parts[1].DeepCopy(),
						expr.Parts[i].DeepCopy(),
					}))
				}
				return toReturn
			}
			return this.Parts[2]
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"{foo[a], foo[b], foo[c]}", "Map[foo, {a, b, c}]"},
			&SameTest{"{foo[a], foo[b], foo[c]}", "foo /@ {a, b, c}"},
			&SameTest{"{2, 4, 9}", "Times /@ {2, 4, 9}"},
			&SameTest{"{foo[{a, b}], foo[c]}", "Map[foo, {{a, b}, c}]"},
			&SameTest{"Map[foo]", "Map[foo]"},
			&SameTest{"foo", "Map[foo, foo]"},
			&SameTest{"Map[foo, foo, foo]", "Map[foo, foo, foo]"},
			&TestComment{"Pure functions are useful with `Map`:"},
			&SameTest{"{4,16}", "Function[x, x^2] /@ {2,4}"},
			&SameTest{"{4,16}", "Function[#^2] /@ {2,4}"},
		},
	})
	defs = append(defs, Definition{
		Name:  "Array",
		Usage: "`Array[f, n]` creates a list of `f[i]`, with `i` = 1 to `n`.",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}

			nInt, nOk := this.Parts[2].(*Integer)
			if nOk {
				n := nInt.Val.Int64()
				toReturn := NewExpression([]Ex{&Symbol{"List"}})
				for i := int64(1); i <= n; i++ {
					toReturn.Parts = append(toReturn.Parts, NewExpression([]Ex{
						this.Parts[1].DeepCopy(),
						&Integer{big.NewInt(i)},
					}))
				}
				return toReturn
			}
			return this.Parts[2]
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"{f[1], f[2], f[3]}", "Array[f, 3]"},
			&SameTest{"Null", "mytest[x_] := 5"},
			&SameTest{"{5, 5, 5}", "Array[mytest, 3]"},
			&SameTest{"{(a + b)[1], (a + b)[2], (a + b)[3]}", "Array[a + b, 3]"},
			&SameTest{"Array[a, a]", "Array[a, a]"},
		},
	})
	defs = append(defs, Definition{
		Name:         "Identity",
		Usage:        "`Identity[expr_]` returns `expr`.",
		SimpleExamples: []TestInstruction{
			&SameTest{"5", "Identity[5]"},
			&SameTest{"a", "Identity[Identity[a]]"},
		},
		Rules: []Rule{
			{"Identity[expr_]", "expr"},
		},
	})
	return
}
