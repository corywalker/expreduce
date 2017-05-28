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

func flattenExpr(src *Expression, dst *Expression, level int64, cl *CASLogger) {
	continueFlatten := level > 0
	for i := 1; i < len(src.Parts); i++ {
		expr, isExpr := src.Parts[i].(*Expression)
		if continueFlatten && isExpr {
			if IsSameQ(src.Parts[0], expr.Parts[0], cl) {
				flattenExpr(expr, dst, level-1, cl)
				continue
			}
		}
		dst.Parts = append(dst.Parts, src.Parts[i])
	}
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
		},
		KnownFailures: []TestInstruction{
			// The following tests will fail until Equal and SameQ can handle
			// multiple inputs:
			&SameTest{"False", "Sequence[2, 3] == Sequence[2, 3]"},
			&SameTest{"True", "Sequence[2, 2] == Sequence[2]"},
			&SameTest{"False", "Sequence[2, 3] === Sequence[2, 3]"},
			&SameTest{"True", "Sequence[2, 2] === Sequence[2]"},
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
	defs = append(defs, Definition{
		Name:       "HoldForm",
		Usage:      "`HoldForm[expr]` prevents automatic evaluation of `expr`. Prints as `expr`.",
		Attributes: []string{"HoldAll"},
		toString: func(this *Expression, form string) (bool, string) {
			if len(this.Parts) != 2 {
				return false, ""
			}
			if form == "FullForm" {
				return false, ""
			}
			return true, this.Parts[1].StringForm(form)
		},
		SimpleExamples: []TestInstruction{
			&StringTest{"5^3", "HoldForm[Power[5, 3]]"},
			&StringTest{"5.^3.", "HoldForm[Power[5., 3.]]"},
		},
	})
	defs = append(defs, Definition{
		Name:  "Flatten",
		Usage: "`Flatten[list]` flattens out lists in `list`.",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) < 2 {
				return this
			}
			level := int64(999999999999)
			if len(this.Parts) > 2 {
				asInt, isInt := this.Parts[2].(*Integer)
				if !isInt {
					return this
				}
				level = int64(asInt.Val.Int64())
			}
			expr, isExpr := this.Parts[1].(*Expression)
			if !isExpr {
				return this
			}
			dst := NewExpression([]Ex{expr.Parts[0]})
			flattenExpr(expr, dst, level, &es.CASLogger)
			return dst
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"Flatten[1]", "Flatten[1]"},
			&TestComment{"Input must be nonatomic:"},
			&SameTest{"{1}", "Flatten[{1}]"},
			&SameTest{"{1}", "Flatten[{{{{1}}}}]"},
			&SameTest{"{1, 2, 3}", "Flatten[{{{{1}, 2}}, 3}]"},
			&SameTest{"{1, 2, 3, 4}", "Flatten[{{{{1}, 2}}, 3, 4}]"},
			&SameTest{"{-1, 1, 2, 3, 4}", "Flatten[{-1, {{{1}, 2}}, 3, 4}]"},
			&TestComment{"A level of zero means no change:"},
			&SameTest{"{-1, {{{1}, 2}}, 3, 4}", "Flatten[{-1, {{{1}, 2}}, 3, 4}, 0]"},
			&SameTest{"{-1, {{1}, 2}, 3, 4}", "Flatten[{-1, {{{1}, 2}}, 3, 4}, 1]"},
			&SameTest{"{-1, {1}, 2, 3, 4}", "Flatten[{-1, {{{1}, 2}}, 3, 4}, 2]"},
			&SameTest{"{-1, 1, 2, 3, 4}", "Flatten[{-1, {{{1}, 2}}, 3, 4}, 3]"},
			&SameTest{"{-1, 1, 2, 3, 4}", "Flatten[{-1, {{{1}, 2}}, 3, 4}, 4]"},
			&SameTest{"Flatten[{-1, {{{1}, 2}}, 3, 4}, a]", "Flatten[{-1, {{{1}, 2}}, 3, 4}, a]"},
			&SameTest{"{-1, foo[{{1}, 2}], 3, 4}", "Flatten[{-1, {foo[{{1}, 2}]}, 3, 4}, 999]"},
			&SameTest{"{-1, foo[{{1}, 2}], 3, 4}", "Flatten[{-1, {foo[{{1}, 2}]}, 3, 4}, 999]"},
			&SameTest{"{-1, 1[{{1}, 2}], 3, 4}", "Flatten[{-1, {1[{{1}, 2}]}, 3, 4}, 999]"},
		},
	})
	defs = append(defs, Definition{
		Name:  "Flat",
		OmitDocumentation: true,
		Tests: []TestInstruction{
			&SameTest{"{ExpreduceFlatFn[a], ExpreduceFlatFn[b, c]}", "foo[ExpreduceFlatFn[a, b, c]] /. foo[ExpreduceFlatFn[x_, y_]] -> {x, y}"},
			&SameTest{"foo[ExpreduceOrderlessFn[a, b, c]]", "foo[ExpreduceOrderlessFn[a, b, c]] /. foo[ExpreduceOrderlessFn[x_, y_]] -> {x, y}"},
			&SameTest{"{x, y}", "foo[ExpreduceFlatFn[a, b, c]] /. foo[ExpreduceFlatFn[_, _]] -> {x, y}"},
			&SameTest{"{a, b, c}", "foo[a + b + c] /. foo[x__ + y__] -> {x, y}"},
			&SameTest{"{a, b + c}", "foo[a + b + c] /. foo[x_ + y_] -> {x, y}"},
			&SameTest{"ExpreduceFlOiFn[{a, b}, c]", "ExpreduceFlOiFn[a, b, c] /. ExpreduceFlOiFn[x_Symbol, y_Symbol] -> {x, y}"},
			&SameTest{"{a, ExpreduceFlOiFn[b, c]}", "ExpreduceFlOiFn[a, b, c] /. ExpreduceFlOiFn[x_Symbol, y_ExpreduceFlOiFn] -> {x, y}"},
		},
	})
	defs = append(defs, Definition{
		Name:  "Orderless",
		OmitDocumentation: true,
		Tests: []TestInstruction{
		},
	})
	defs = append(defs, Definition{
		Name:  "OneIdentity",
		OmitDocumentation: true,
		Tests: []TestInstruction{
			&SameTest{"False", "MatchQ[ExpreduceFlOrFn[a, a^(-1)], ExpreduceFlOrFn[a_, a_^-1, rest___]]"},
			&SameTest{"True", "MatchQ[ExpreduceFlOrOiFn[a, a^(-1)], ExpreduceFlOrOiFn[a_, a_^-1, rest___]]"},
			&SameTest{"True", "MatchQ[foo[ExpreduceFlOiFn[ExpreduceFlOiFn2[a]], a], foo[ExpreduceFlOiFn[ExpreduceFlOiFn2[a_]], a_]]"},
			&SameTest{"False", "MatchQ[foo[ExpreduceFlatFn[ExpreduceFlatFn2[a]], a], foo[ExpreduceFlatFn[ExpreduceFlatFn2[a_]], a_]]"},
			&SameTest{"a", "ExpreduceFlOiFn[ExpreduceFlOiFn2[a]] /. ExpreduceFlOiFn[ExpreduceFlOiFn2[a_]] -> a"},
			&SameTest{"ExpreduceFlatFn2[a]", "ExpreduceFlatFn[ExpreduceFlatFn2[a]] /. ExpreduceFlatFn[ExpreduceFlatFn2[a_]] -> a"},
			&SameTest{"a", "ExpreduceOneIdentityFn[ExpreduceOneIdentityFn2[a]] /. ExpreduceOneIdentityFn[ExpreduceOneIdentityFn2[a_]] -> a"},
			&SameTest{"True", "MatchQ[foo[ExpreduceFlOiFn[ExpreduceFlOiFn2[a]], a], foo[ExpreduceFlOiFn[ExpreduceFlOiFn2[a__]], a__]]"},
		},
	})
	return
}
