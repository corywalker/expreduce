package expreduce

import "math/big"

func dimensions(ex *Expression, level int, cl *CASLogger) []int64 {
	head := ex.Parts[0]
	dims := []int64{int64(len(ex.Parts) - 1)}
	nextDims := []int64{}
	for i := 1; i < len(ex.Parts); i++ {
		subHead, isSubHead := headExAssertion(ex.Parts[i], head, cl)
		if !isSubHead {
			return dims
		} else {
			currDims := dimensions(subHead, level+1, cl)
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
	toReturn := NewExpression([]Ex{
		&Symbol{"System`List"},
	})

	for _, i := range ints {
		toReturn.Parts = append(toReturn.Parts, &Integer{big.NewInt(i)})
	}
	return toReturn
}

// This function assumes that mat is a matrix and that i and j are not out of
// bounds. i and j are 1-indexed.
func (mat *Expression) matrix2dGetElem(i, j int64) Ex {
	return (mat.Parts[i].(*Expression)).Parts[j]
}

func calcIJ(i, j, innerDim int64, a, b *Expression) Ex {
	toReturn := NewExpression([]Ex{&Symbol{"System`Plus"}})
	for pairI := int64(1); pairI <= innerDim; pairI++ {
		toAdd := NewExpression([]Ex{&Symbol{"System`Times"}})
		toAdd.appendEx(a.matrix2dGetElem(i, pairI))
		toAdd.appendEx(b.matrix2dGetElem(pairI, j))
		toReturn.appendEx(toAdd)
	}
	return toReturn
}

func GetMatrixDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name:    "Inverse",
		Usage:   "`Inverse[mat]` finds the inverse of the square matrix `mat`.",
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
				return NewExpression([]Ex{&Symbol{"System`List"}})
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
		Name:         "VectorQ",
		Usage:        "`VectorQ[expr]` returns True if `expr` is a vector, False otherwise.",
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
		Name:         "MatrixQ",
		Usage:        "`MatrixQ[expr]` returns True if `expr` is a 2D matrix, False otherwise.",
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
	defs = append(defs, Definition{
		Name:       "Dot",
		Usage:      "`a.b` computes the product of `a` and `b` for vectors and matrices.",
		Attributes: []string{"Flat", "OneIdentity"},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) == 2 {
				return this.Parts[1]
			}
			if len(this.Parts) != 3 {
				return this
			}
			aIsVector := vectorQ(this.Parts[1])
			bIsVector := vectorQ(this.Parts[2])
			if aIsVector && bIsVector {
				aVector := this.Parts[1].(*Expression)
				bVector := this.Parts[2].(*Expression)
				if len(aVector.Parts) != len(bVector.Parts) {
					return this
				}
				vecLen := len(aVector.Parts) - 1
				toReturn := NewExpression([]Ex{&Symbol{"System`Plus"}})
				for i := 0; i < vecLen; i++ {
					toReturn.appendEx(NewExpression([]Ex{
						&Symbol{"System`Times"},
						aVector.Parts[i+1],
						bVector.Parts[i+1],
					}))
				}
				return toReturn
			}
			aIsMatrix := matrixQ(this.Parts[1], &es.CASLogger)
			bIsMatrix := matrixQ(this.Parts[2], &es.CASLogger)
			if aIsMatrix && bIsMatrix {
				aEx := this.Parts[1].(*Expression)
				bEx := this.Parts[2].(*Expression)
				aDims := dimensions(aEx, 0, &es.CASLogger)
				bDims := dimensions(bEx, 0, &es.CASLogger)
				if len(aDims) != 2 || len(bDims) != 2 {
					return this
				}
				aH, aW := aDims[0], aDims[1]
				bH, bW := bDims[0], bDims[1]
				if aW != bH {
					return this
				}
				toReturn := NewExpression([]Ex{&Symbol{"System`List"}})
				for i := int64(1); i <= aH; i++ {
					row := NewExpression([]Ex{&Symbol{"System`List"}})
					for j := int64(1); j <= bW; j++ {
						//row.appendEx(&Integer{big.NewInt(0)})
						row.appendEx(calcIJ(i, j, aW, aEx, bEx))
					}
					toReturn.appendEx(row)
				}
				return toReturn
			}
			return this
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"a c + b d", "{a, b}.{c, d}"},
			&SameTest{"{a, b}.{c, d, e}", "{a, b}.{c, d, e}"},
			&SameTest{"Dot[1, {c, d, e}]", "Dot[1, {c, d, e}]"},
			&SameTest{"0", "Dot[{}, {}]"},
			&SameTest{"{{a, b}, {c, d}}.{e, f, g}", "{{a, b}, {c, d}}.{e, f, g}"},
			&SameTest{"{a, b}", "Dot[{a, b}]"},
			&SameTest{"a", "Dot[a]"},
			&SameTest{"1", "Dot[1]"},

			// Matrix multiplication
			&SameTest{"{{a e + b g, a f + b h}, {c e + d g, c f + d h}}", "{{a, b}, {c, d}}.{{e, f}, {g, h}}"},
			&SameTest{"{{a e + b f}, {c e + d f}}", "{{a, b}, {c, d}}.{{e}, {f}}"},
			&SameTest{"{{a, b}, {c, d}}.{{e, f}}", "{{a, b}, {c, d}}.{{e, f}}"},
		},
		KnownFailures: []TestInstruction{
			&SameTest{"{a e + b f, c e + d f}", "{{a, b}, {c, d}}.{e, f}"},
			&SameTest{"{a e + c f, b e + d f}", "{e, f}.{{a, b}, {c, d}}"},
		},
	})
	defs = append(defs, Definition{
		Name:  "Transpose",
		Usage: "`Transpose[mat]` transposes the first two levels of `mat`",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}
			l, isL := ContextedHeadAssertion(this.Parts[1], "System`List")
			if !isL {
				return this
			}
			dims := dimensions(l, 0, &es.CASLogger)
			if len(dims) < 2 {
				return this
			}
			h, w := dims[0], dims[1]
			toReturn := NewExpression([]Ex{&Symbol{"System`List"}})
			for tI := int64(1); tI <= w; tI++ {
				tRow := NewExpression([]Ex{&Symbol{"System`List"}})
				for tJ := int64(1); tJ <= h; tJ++ {
					tRow.appendEx(l.matrix2dGetElem(tJ, tI))
				}
				toReturn.appendEx(tRow)
			}
			return toReturn
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"Transpose[{a, b}]", "Transpose[{a, b}]"},
			&SameTest{"{{a, b}}", "Transpose[{{a}, {b}}]"},
			&SameTest{"{{a}, {b}}", "Transpose[{{a, b}}]"},
			&SameTest{"{{{a}}, {{b}}}", "Transpose[{{{a}, {b}}}]"},
			&SameTest{"Transpose[a]", "Transpose[a]"},
		},
	})
	return
}
