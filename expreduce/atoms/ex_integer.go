package atoms

import (
	"fmt"
	"hash/fnv"
	"math/big"

	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

// Integer numbers represented by big.Int
type Integer struct {
	Val        *big.Int
	cachedHash uint64
}

/*func (f *Integer) StringForm(params ToStringParams) string {
	return fmt.Sprintf("%d", f.Val)
}*/

func (thisInt *Integer) StringForm(params expreduceapi.ToStringParams) string {
	return fmt.Sprintf("%d", thisInt.Val)
}

func (thisInt *Integer) String() string {
	return thisInt.StringForm(defaultStringParams())
}

func (thisInt *Integer) IsEqual(other expreduceapi.Ex) string {
	otherConv, ok := other.(*Integer)
	if !ok {
		otherFlt, ok := other.(*Flt)
		if ok {
			thisIntAsFlt := big.NewFloat(0)
			thisIntAsFlt.SetInt(thisInt.Val)
			if thisIntAsFlt.Cmp(otherFlt.Val) == 0 {
				return "EQUAL_TRUE"
			}
		}
		return "EQUAL_UNK"
	}
	if thisInt.Val.Cmp(otherConv.Val) != 0 {
		return "EQUAL_FALSE"
	}
	return "EQUAL_TRUE"
}

func (thisInt *Integer) DeepCopy() expreduceapi.Ex {
	tmp := big.NewInt(0)
	tmp.Set(thisInt.Val)
	return &Integer{Val: tmp, cachedHash: thisInt.cachedHash}
}

func (thisInt *Integer) Copy() expreduceapi.Ex {
	return thisInt
}

func (thisInt *Integer) NeedsEval() bool {
	return false
}

func NewInteger(i *big.Int) *Integer {
	return &Integer{Val: i}
}

func NewInt(i int64) *Integer {
	return NewInteger(big.NewInt(i))
}

func (thisInt *Integer) Hash() uint64 {
	if thisInt.cachedHash > 0 {
		return thisInt.cachedHash
	}
	h := fnv.New64a()
	h.Write([]byte{242, 99, 84, 113, 102, 46, 118, 94})
	bytes, _ := thisInt.Val.GobEncode()
	h.Write(bytes)
	thisInt.cachedHash = h.Sum64()
	return h.Sum64()
}

func (thisInt *Integer) asBigFloat() *big.Float {
	newfloat := big.NewFloat(0)
	newfloat.SetInt(thisInt.Val)
	return newfloat
}

func (thisInt *Integer) addI(i *Integer) {
	thisInt.Val.Add(thisInt.Val, i.Val)
	thisInt.cachedHash = 0
}

func (thisInt *Integer) mulI(i *Integer) {
	thisInt.Val.Mul(thisInt.Val, i.Val)
	thisInt.cachedHash = 0
}
