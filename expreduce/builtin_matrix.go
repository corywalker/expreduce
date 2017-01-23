package expreduce

import "math/big"

func dimensions(ex *Expression, level int, cl *CASLogger) []int64 {
	head := ex.Parts[0]
	dims := []int64{int64(len(ex.Parts)-1)}
	nextDims := []int64{}
	for i := 1; i < len(ex.Parts); i++ {
		subHead, isSubHead := headExAssertion(ex.Parts[i], head, cl)
		if !isSubHead {
			return dims
		} else {
			currDims := dimensions(subHead, level + 1, cl)
			if i != 1 {
				if len(nextDims) > len(currDims) {
					nextDims = nextDims[:len(currDims)-1]
				}
				for i := range nextDims {
					if nextDims[i] != currDims[i] {
						return dims
					}
				}
			}
			nextDims = currDims
		}
	}
	return append(dims, nextDims...)
}

func intSliceToList(ints []int64) Ex {
	toReturn := &Expression{[]Ex{
		&Symbol{"List"},
	}}
	for _, i := range ints {
		toReturn.Parts = append(toReturn.Parts, &Integer{big.NewInt(i)})
	}
	return toReturn
}

func GetMatrixDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name:  "Inverse",
		Usage: "`Inverse[mat]` finds the inverse of the square matrix `mat`.",
		Details: "The row-reduce method has not been added yet, but the shortcuts to finding the inverses of matrices up to 3x3 have been added.",
		Rules: []Rule{
			{"Inverse[{{a_}}]", "{{1/a}}"},
			{"Inverse[{{a_, b_}, {c_, d_}}]", "{{d/(-b c + a d), -(b/(-b c + a d))}, {-(c/(-b c + a d)), a/(-b c + a d)}}"},
			{"Inverse[{{a_, b_, c_}, {d_, e_, f_}, {h_, i_, j_}}]", "{{(-f i + e j)/(-c e h + b f h + c d i - a f i - b d j + a e j), (c i - b j)/(-c e h + b f h + c d i - a f i - b d j + a e j), (-c e + b f)/(-c e h + b f h + c d i - a f i - b d j + a e j)}, {(f h - d j)/(-c e h + b f h + c d i - a f i - b d j + a e j), (-c h + a j)/(-c e h + b f h + c d i - a f i - b d j + a e j), (c d - a f)/(-c e h + b f h + c d i - a f i - b d j + a e j)}, {(-e h + d i)/(-c e h + b f h + c d i - a f i - b d j + a e j), (b h - a i)/(-c e h + b f h + c d i - a f i - b d j + a e j), (-b d + a e)/(-c e h + b f h + c d i - a f i - b d j + a e j)}}"},
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"{{-2, 1}, {3/2, -(1/2)}}", "Inverse[{{1, 2}, {3, 4}}]"},
			&SameTest{"{{2/5, -(1/5), 0}, {-(1/15), 19/45, -(1/9)}, {-(1/15), -(11/45), 2/9}}", "Inverse[{{3, 2, 1}, {1, 4, 2}, {2, 5, 7}}]"},
		},
		FurtherExamples: []TestInstruction{
			&TestComment{"Symbolic elements are handled correctly:"},
			&SameTest{"Inverse[{{b}}]", "{{1/b}}"},
		},
	})
	defs = append(defs, Definition{
		Name:  "Dimensions",
		Usage: "`Dimensions[expr]` finds the dimensions of `expr`.",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}
			expr, isExpr := this.Parts[1].(*Expression)
			if !isExpr {
				return &Expression{[]Ex{&Symbol{"List"}}}
			}
			return intSliceToList(dimensions(expr, 0, &es.CASLogger))
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"{2, 2}", "Dimensions[{{1, 3}, {1, 2}}]"},
			&SameTest{"{2}", "Dimensions[{{{1, 2}, {3, 2}}, {{1, 2}}}]"},
		},
		FurtherExamples: []TestInstruction{
			&SameTest{"{}", "Dimensions[foo]"},
			&TestComment{"`Dimensions` works with any head, not just `List`:"},
			&SameTest{"{0}", "Dimensions[foo[]]"},
		},
		Tests: []TestInstruction{
			&SameTest{"{2}", "Dimensions[{1, 2}]"},
			&SameTest{"{0}", "Dimensions[{}]"},
			&SameTest{"{1}", "Dimensions[foo[{1}]]"},
			&SameTest{"{1, 1}", "Dimensions[{{1}}]"},
			&SameTest{"{2, 1}", "Dimensions[{{1}, {1}}]"},
			&SameTest{"{2}", "Dimensions[{{1}, {1, 2}}]"},
			&SameTest{"{2, 2}", "Dimensions[{{1, 3}, {1, 2}}]"},
			&SameTest{"{2, 2, 1}", "Dimensions[{{{1}, {3}}, {{1}, {2}}}]"},
			&SameTest{"{2, 2, 2}", "Dimensions[{{{1, 2}, {3, 2}}, {{1, 2}, {2, 2}}}]"},
			&SameTest{"{2}", "Dimensions[{{{1, 2}, {3, 2}}, {{1, 2}}}]"},
			&SameTest{"{2, 2, 2}", "Dimensions[{{{1, 2}, {3, 2}}, {{1, 2}, {foo, 2}}}]"},
			&SameTest{"{2, 2}", "Dimensions[{{{1, 2}, {3, 2}}, {{1, 2}, foo[foo, 2]}}]"},
			&SameTest{"{1, 2, 0}", "Dimensions[{{{}, {}}}]"},
			&SameTest{"{1, 2}", "Dimensions[{{{}, foo[x]}}]"},
		},
	})
	defs = append(defs, Definition{
		Name:  "VectorQ",
		Usage: "`VectorQ[expr]` returns True if `expr` is a vector, False otherwise.",
		legacyEvalFn: singleParamQEval(vectorQ),
		SimpleExamples: []TestInstruction{
			&SameTest{"True", "VectorQ[{1, 2, c}]"},
			&SameTest{"True", "VectorQ[{1, 2, foo[a]}]"},
			&SameTest{"False", "VectorQ[foo[1, 2, 3]]"},
			&SameTest{"False", "VectorQ[{1, 2, 3, {}}]"},
			&SameTest{"True", "VectorQ[{f[a], f[b]}]"},
			&SameTest{"True", "VectorQ[{a, c}]"},
			&SameTest{"True", "VectorQ[{}]"},
		},
	})
	defs = append(defs, Definition{
		Name:  "MatrixQ",
		Usage: "`MatrixQ[expr]` returns True if `expr` is a 2D matrix, False otherwise.",
		legacyEvalFn: singleParamQLogEval(matrixQ),
		SimpleExamples: []TestInstruction{
			&SameTest{"False", "MatrixQ[{}]"},
			&SameTest{"True", "MatrixQ[{{}}]"},
			&SameTest{"True", "MatrixQ[{{a}}]"},
			&SameTest{"False", "MatrixQ[{{{}}}]"},
			&SameTest{"False", "MatrixQ[{{{a}}}]"},
			&SameTest{"True", "MatrixQ[{{a}, {b}}]"},
			&SameTest{"True", "MatrixQ[{{a, b}, {c, d}}]"},
			&SameTest{"False", "MatrixQ[{{a, b, e}, {c, d}}]"},
			&SameTest{"True", "MatrixQ[{{a, b, e}, {c, d, f}}]"},
			&SameTest{"False", "MatrixQ[{{{a}, {b}}, {{c}, {d}}}]"},
			&SameTest{"True", "MatrixQ[{{a, b, e}}]"},
		},
	})
	return
}
