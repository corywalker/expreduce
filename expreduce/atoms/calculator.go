package atoms

import "github.com/corywalker/expreduce/pkg/expreduceapi"

type foldFn int

const (
	// FoldFnAdd designates that values should be added.
	FoldFnAdd foldFn = iota
	// FoldFnMul designates that values should be multiplied.
	FoldFnMul
)

func typedRealPart(
	fn foldFn,
	i *Integer,
	r *Rational,
	f *Flt,
	c *Complex,
) expreduceapi.Ex {
	if c != nil {
		toReturn := c
		if f != nil {
			if fn == FoldFnAdd {
				toReturn.addF(f)
			} else if fn == FoldFnMul {
				toReturn.mulF(f)
			}
		}
		if r != nil {
			if fn == FoldFnAdd {
				toReturn.addR(r)
			} else if fn == FoldFnMul {
				toReturn.mulR(r)
			}
		}
		if i != nil {
			if fn == FoldFnAdd {
				toReturn.addI(i)
			} else if fn == FoldFnMul {
				toReturn.mulI(i)
			}
		}
		return toReturn
	}
	if f != nil {
		toReturn := f
		if r != nil {
			if fn == FoldFnAdd {
				toReturn.addR(r)
			} else if fn == FoldFnMul {
				toReturn.mulR(r)
			}
		}
		if i != nil {
			if fn == FoldFnAdd {
				toReturn.addI(i)
			} else if fn == FoldFnMul {
				toReturn.mulI(i)
			}
		}
		return toReturn
	}
	if r != nil {
		toReturn := r
		if i != nil {
			if fn == FoldFnAdd {
				toReturn.addI(i)
			} else if fn == FoldFnMul {
				toReturn.mulI(i)
			}
		}
		return toReturn
	}
	if i != nil {
		return i
	}
	return nil
}

func ComputeNumericPart(
	fn foldFn,
	e expreduceapi.ExpressionInterface,
) (expreduceapi.Ex, int) {
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
				foldedInt.addI(asInt)
			} else if fn == FoldFnMul {
				foldedInt.mulI(asInt)
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
				foldedRat.addR(asRat)
			} else if fn == FoldFnMul {
				foldedRat.mulR(asRat)
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
				foldedFlt.addF(asFlt)
			} else if fn == FoldFnMul {
				foldedFlt.mulF(asFlt)
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
				foldedComp.addC(asComp)
			} else if fn == FoldFnMul {
				foldedComp.mulC(asComp)
			}
			continue
		}
		return typedRealPart(fn, foldedInt, foldedRat, foldedFlt, foldedComp), i
	}
	return typedRealPart(fn, foldedInt, foldedRat, foldedFlt, foldedComp), -1
}
