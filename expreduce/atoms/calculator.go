package atoms

import "github.com/corywalker/expreduce/pkg/expreduceapi"

type FoldFn int

const (
	FoldFnAdd FoldFn = iota
	FoldFnMul
)

func typedRealPart(fn FoldFn, i *Integer, r *Rational, f *Flt, c *Complex) expreduceapi.Ex {
	if c != nil {
		toReturn := c
		if f != nil {
			if fn == FoldFnAdd {
				toReturn.AddF(f)
			} else if fn == FoldFnMul {
				toReturn.MulF(f)
			}
		}
		if r != nil {
			if fn == FoldFnAdd {
				toReturn.AddR(r)
			} else if fn == FoldFnMul {
				toReturn.MulR(r)
			}
		}
		if i != nil {
			if fn == FoldFnAdd {
				toReturn.AddI(i)
			} else if fn == FoldFnMul {
				toReturn.MulI(i)
			}
		}
		return toReturn
	}
	if f != nil {
		toReturn := f
		if r != nil {
			if fn == FoldFnAdd {
				toReturn.AddR(r)
			} else if fn == FoldFnMul {
				toReturn.MulR(r)
			}
		}
		if i != nil {
			if fn == FoldFnAdd {
				toReturn.AddI(i)
			} else if fn == FoldFnMul {
				toReturn.MulI(i)
			}
		}
		return toReturn
	}
	if r != nil {
		toReturn := r
		if i != nil {
			if fn == FoldFnAdd {
				toReturn.AddI(i)
			} else if fn == FoldFnMul {
				toReturn.MulI(i)
			}
		}
		return toReturn
	}
	if i != nil {
		return i
	}
	return nil
}

func ComputeNumericPart(fn FoldFn, e expreduceapi.ExpressionInterface) (expreduceapi.Ex, int) {
	var foldedInt *Integer
	var foldedRat *Rational
	var foldedFlt *Flt
	var foldedComp *Complex
	for i := 1; i < len(e.GetParts()); i++ {
		// TODO: implement short circuiting if we encounter a zero while
		// multiplying.
		asInt, isInt := e.GetParts()[i].(*Integer)
		if isInt {
			if foldedInt == nil {
				// Try deepcopy if problems. I think this does not cause
				// problems now because we will only modify the value if we end
				// up creating an entirely new expression.
				foldedInt = asInt.DeepCopy().(*Integer)
				continue
			}
			if fn == FoldFnAdd {
				foldedInt.AddI(asInt)
			} else if fn == FoldFnMul {
				foldedInt.MulI(asInt)
			}
			continue
		}
		asRat, isRat := e.GetParts()[i].(*Rational)
		if isRat {
			if foldedRat == nil {
				foldedRat = asRat.DeepCopy().(*Rational)
				continue
			}
			if fn == FoldFnAdd {
				foldedRat.AddR(asRat)
			} else if fn == FoldFnMul {
				foldedRat.MulR(asRat)
			}
			continue
		}
		asFlt, isFlt := e.GetParts()[i].(*Flt)
		if isFlt {
			if foldedFlt == nil {
				foldedFlt = asFlt.DeepCopy().(*Flt)
				continue
			}
			if fn == FoldFnAdd {
				foldedFlt.AddF(asFlt)
			} else if fn == FoldFnMul {
				foldedFlt.MulF(asFlt)
			}
			continue
		}
		asComp, isComp := e.GetParts()[i].(*Complex)
		if isComp {
			if foldedComp == nil {
				foldedComp = asComp.DeepCopy().(*Complex)
				continue
			}
			if fn == FoldFnAdd {
				foldedComp.AddC(asComp)
			} else if fn == FoldFnMul {
				foldedComp.MulC(asComp)
			}
			continue
		}
		return typedRealPart(fn, foldedInt, foldedRat, foldedFlt, foldedComp), i
	}
	return typedRealPart(fn, foldedInt, foldedRat, foldedFlt, foldedComp), -1
}
