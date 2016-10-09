package cas

import "math/big"

func compareStrings(a string, b string) int64 {
	minchars := Min(len(a), len(b))
	for i := 0 ; i < minchars ; i++ {
		if a[i] > b[i] {
			return -1
		} else if a[i] < b[i] {
			return 1
		}
	}
	if len(a) > len(b) {
		return -1
	} else if len(a) < len(b) {
		return 1
	}
	return 0
}

func ExOrder(a Ex, b Ex) int64 {
	// Support Flt, Integer, Expression, Symbol
	// Merge Integer into Flt
	// Need to support the following combinations
	// ff,fs,fe,sf,ss,se,ef,es,ee

	aAsSymbol, aIsSymbol := a.(*Symbol)
	bAsSymbol, bIsSymbol := b.(*Symbol)

	aAsFlt, aIsFlt := a.(*Flt)
	bAsFlt, bIsFlt := b.(*Flt)
	aAsInteger, aIsInteger := a.(*Integer)
	bAsInteger, bIsInteger := b.(*Integer)
	if aIsInteger {
		aAsFlt, aIsFlt = IntegerToFlt(aAsInteger)
	}
	if bIsInteger {
		bAsFlt, bIsFlt = IntegerToFlt(bAsInteger)
	}

	if aIsFlt && bIsFlt {
		initCmp := int64(bAsFlt.Val.Cmp(aAsFlt.Val))
		if initCmp == 0 && (aIsInteger && !bIsInteger) {
			return 1
		}
		if initCmp == 0 && (!aIsInteger && bIsInteger) {
			return -1
		}
		return initCmp
	}

	if aIsFlt && bIsSymbol {
		return 1
	} else if aIsSymbol && bIsFlt {
		return -1
	}

	if aIsSymbol && bIsSymbol {
		return compareStrings(aAsSymbol.Name, bAsSymbol.Name)
	}

	aAsExp, aIsExp := a.(*Expression)
	bAsExp, bIsExp := b.(*Expression)
	if aIsExp && bIsExp {
		for i := 0; i < Min(len(aAsExp.Parts), len(bAsExp.Parts)); i++ {
			o := ExOrder(aAsExp.Parts[i], bAsExp.Parts[i])
			if o != 0 {
				return o
			}
		}
		if len(aAsExp.Parts) < len(bAsExp.Parts) {
			return 1
		} else if len(aAsExp.Parts) > len(bAsExp.Parts) {
			return -1
		} else {
			return 0
		}
	}

	if aIsFlt && bIsExp {
		return 1
	} else if aIsExp && bIsFlt {
		return -1
	}
	if aIsSymbol && bIsExp {
		return 1
	} else if aIsExp && bIsSymbol {
		return -1
	}

	// Do not support strings. Any comparison with these will go here.
	return -2
}

func (this *Expression) EvalOrder(es *EvalState) Ex {
	if len(this.Parts) != 3 {
		return this
	}

	toreturn := ExOrder(this.Parts[1], this.Parts[2])
	return &Integer{big.NewInt(toreturn)}
}
