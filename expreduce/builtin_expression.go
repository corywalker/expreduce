package expreduce

import "math/big"

func CalcDepth(ex Ex) int {
	expr, isExpr := ex.(*Expression)
	if !isExpr {
		return 1
	}
	theMax := 1
	// Find max depth of params. Heads are not counted.
	for i := 1; i < len(expr.Parts); i++ {
		theMax = Max(theMax, CalcDepth(expr.Parts[i]))
	}
	return theMax + 1
}

func GetExpressionDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name:  "Head",
		Usage: "`Head[expr]` returns the head of the expression.",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}

			_, IsFlt := this.Parts[1].(*Flt)
			if IsFlt {
				return &Symbol{"Real"}
			}
			_, IsInteger := this.Parts[1].(*Integer)
			if IsInteger {
				return &Symbol{"Integer"}
			}
			_, IsString := this.Parts[1].(*String)
			if IsString {
				return &Symbol{"String"}
			}
			_, IsSymbol := this.Parts[1].(*Symbol)
			if IsSymbol {
				return &Symbol{"Symbol"}
			}
			_, IsRational := this.Parts[1].(*Rational)
			if IsRational {
				return &Symbol{"Rational"}
			}
			asExpr, IsExpression := this.Parts[1].(*Expression)
			if IsExpression {
				return asExpr.Parts[0].DeepCopy()
			}
			return this
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"f", "Head[f[x]]"},
			&SameTest{"Symbol", "Head[x]"},
			&SameTest{"List", "Head[{x}]"},
			&SameTest{"Plus", "Head[a + b]"},
			&SameTest{"Integer", "Head[1]"},
			&SameTest{"Real", "Head[1.]"},
			&SameTest{"Rational", "Head[2/7]"},
			&SameTest{"Rational", "Head[1/7]"},
			&SameTest{"String", "Head[\"1\"]"},
			&SameTest{"Plus", "Head[Head[(a + b)[x]]]"},
		},
	})
	defs = append(defs, Definition{
		Name:  "Depth",
		Usage: "`Depth[expr]` returns the depth of `expr`.",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}
			return &Integer{big.NewInt(int64(CalcDepth(this.Parts[1])))}
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"1", "Depth[foo]"},
			&SameTest{"2", "Depth[{foo}]"},
			&SameTest{"2", "Depth[bar[foo, bar]]"},
			&SameTest{"3", "Depth[foo[foo[]]]"},
			&SameTest{"1", "Depth[3]"},
			&SameTest{"1", "Depth[3.5]"},
			&SameTest{"1", "Depth[3/5]"},
			&SameTest{"2", "Depth[foo[{{{}}}][]]"},
		},
	})
	defs = append(defs, Definition{
		Name:  "Length",
		Usage: "`Length[expr]` returns the length of `expr`.",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}

			expr, isExpr := this.Parts[1].(*Expression)
			if isExpr {
				return &Integer{big.NewInt(int64(len(expr.Parts) - 1))}
			}
			return this
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"4", "Length[{1,2,3,4}]"},
			&SameTest{"0", "Length[{}]"},
			&SameTest{"1", "Length[{5}]"},
		},
		FurtherExamples: []TestInstruction{
			&TestComment{"`expr` need not have a `List` head:"},
			&SameTest{"2", "Length[foo[1, 2]]"},
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
