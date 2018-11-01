package atoms

import (
	"math"

	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

// IsSameQ returns if two expressions are the same. It is mostly just a
// comparison of the hash values but it does include special handling for
// floats.
func IsSameQ(a expreduceapi.Ex, b expreduceapi.Ex) bool {
	aFlt, aIsFlt := a.(*Flt)
	bFlt, bIsFlt := b.(*Flt)

	if aIsFlt && bIsFlt {
		// This is important, without it e.g. NestWhileList[(# + 3/#)/2 &, 1.0, UnsameQ, 2] never converges
		// https://stackoverflow.com/questions/46136886/comparing-floats-by-ignoring-last-bit-in-golang
		aVal, _ := aFlt.Val.Float64()
		bVal, _ := bFlt.Val.Float64()

		if !(math.IsInf(aVal, 0) || math.IsInf(bVal, 0)) {
			return almostEqual(aVal, bVal)
		}
	}
	return a.Hash() == b.Hash()
}

func almostEqual(a, b float64) bool {
	ai, bi := int64(math.Float64bits(a)), int64(math.Float64bits(b))
	return a == b || -1 <= ai-bi && ai-bi <= 1
}
