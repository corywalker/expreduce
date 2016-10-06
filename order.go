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

func ExOrder(a Ex, b Ex, es *EvalState) int64 {
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

	if aIsSymbol && bIsSymbol {
		es.log.Debugf("%v %v", aAsSymbol.Name, bAsSymbol.Name)
		return compareStrings(aAsSymbol.Name, bAsSymbol.Name)
	}

	return -2
}

func (this *Expression) EvalOrder(es *EvalState) Ex {
	if len(this.Parts) != 3 {
		return this
	}

	toreturn := ExOrder(this.Parts[1], this.Parts[2], es)
	return &Integer{big.NewInt(toreturn)}
}
