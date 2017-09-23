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
		NewSymbol("System`List"),
	})

	for _, i := range ints {
		toReturn.Parts = append(toReturn.Parts, NewInteger(big.NewInt(i)))
	}
	return toReturn
}

// This function assumes that mat is a matrix and that i and j are not out of
// bounds. i and j are 1-indexed.
func (mat *Expression) matrix2dGetElem(i, j int64) Ex {
	return (mat.Parts[i].(*Expression)).Parts[j]
}

func calcIJ(i, j, innerDim int64, a, b *Expression) Ex {
	toReturn := NewExpression([]Ex{NewSymbol("System`Plus")})
	for pairI := int64(1); pairI <= innerDim; pairI++ {
		toAdd := NewExpression([]Ex{NewSymbol("System`Times")})
		toAdd.appendEx(a.matrix2dGetElem(i, pairI))
		toAdd.appendEx(b.matrix2dGetElem(pairI, j))
		toReturn.appendEx(toAdd)
	}
	return toReturn
}

func GetMatrixDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name:    "Inverse",
		Details: "The row-reduce method has not been added yet, but the shortcuts to finding the inverses of matrices up to 3x3 have been added.",
	})
	defs = append(defs, Definition{
		Name: "Dimensions",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}
			expr, isExpr := this.Parts[1].(*Expression)
			if !isExpr {
				return NewExpression([]Ex{NewSymbol("System`List")})
			}
			return intSliceToList(dimensions(expr, 0, &es.CASLogger))
		},
	})
	defs = append(defs, Definition{
		Name:         "VectorQ",
		legacyEvalFn: singleParamQEval(vectorQ),
	})
	defs = append(defs, Definition{
		Name:         "MatrixQ",
		legacyEvalFn: singleParamQLogEval(matrixQ),
	})
	defs = append(defs, Definition{
		Name: "Dot",
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
				toReturn := NewExpression([]Ex{NewSymbol("System`Plus")})
				for i := 0; i < vecLen; i++ {
					toReturn.appendEx(NewExpression([]Ex{
						NewSymbol("System`Times"),
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
				toReturn := NewExpression([]Ex{NewSymbol("System`List")})
				for i := int64(1); i <= aH; i++ {
					row := NewExpression([]Ex{NewSymbol("System`List")})
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
	})
	defs = append(defs, Definition{
		Name: "Transpose",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}
			l, isL := HeadAssertion(this.Parts[1], "System`List")
			if !isL {
				return this
			}
			dims := dimensions(l, 0, &es.CASLogger)
			if len(dims) < 2 {
				return this
			}
			h, w := dims[0], dims[1]
			toReturn := NewExpression([]Ex{NewSymbol("System`List")})
			for tI := int64(1); tI <= w; tI++ {
				tRow := NewExpression([]Ex{NewSymbol("System`List")})
				for tJ := int64(1); tJ <= h; tJ++ {
					tRow.appendEx(l.matrix2dGetElem(tJ, tI))
				}
				toReturn.appendEx(tRow)
			}
			return toReturn
		},
	})
	return
}
