package expreduce

import (
	"fmt"
	"hash/fnv"
	"math/big"
)

// Integer numbers represented by big.Int
type Integer struct {
	Val        *big.Int
	cachedHash uint64
}

func (f *Integer) Eval(es *EvalState) Ex {
	return f
}

/*func (f *Integer) StringForm(params ToStringParams) string {
	return fmt.Sprintf("%d", f.Val)
}*/

func (i *Integer) StringForm(params ToStringParams) string {
	if i.Val.Cmp(big.NewInt(0)) < 0 {
		if needsParens("System`Times", params.previousHead) {
			if params.form == "TeXForm" {
				return fmt.Sprintf("{(%d)}", i.Val)
			}
			return fmt.Sprintf("(%d)", i.Val)
		}
	}
	return fmt.Sprintf("%d", i.Val)
}

func (this *Integer) String(esi EvalStateInterface) string {
	context, contextPath := DefaultStringFormArgs()
	return this.StringForm(ToStringParams{form: "InputForm", context: context, contextPath: contextPath, esi: esi})
}

func (this *Integer) IsEqual(other Ex) string {
	otherConv, ok := other.(*Integer)
	if !ok {
		otherFlt, ok := other.(*Flt)
		if ok {
			thisAsFlt := big.NewFloat(0)
			thisAsFlt.SetInt(this.Val)
			if thisAsFlt.Cmp(otherFlt.Val) == 0 {
				return "EQUAL_TRUE"
			}
		}
		return "EQUAL_UNK"
	}
	if this.Val.Cmp(otherConv.Val) != 0 {
		return "EQUAL_FALSE"
	}
	return "EQUAL_TRUE"
}

func (this *Integer) DeepCopy() Ex {
	tmp := big.NewInt(0)
	tmp.Set(this.Val)
	return &Integer{Val: tmp, cachedHash: this.cachedHash}
}

func (this *Integer) Copy() Ex {
	return this
}

func (this *Integer) NeedsEval() bool {
	return false
}

func NewInteger(i *big.Int) *Integer {
	return &Integer{Val: i}
}

func NewInt(i int64) *Integer {
	return NewInteger(big.NewInt(i))
}

func (this *Integer) Hash() uint64 {
	if this.cachedHash > 0 {
		return this.cachedHash
	}
	h := fnv.New64a()
	h.Write([]byte{242, 99, 84, 113, 102, 46, 118, 94})
	bytes, _ := this.Val.MarshalText()
	h.Write(bytes)
	this.cachedHash = h.Sum64()
	return h.Sum64()
}

func (this *Integer) AsBigFloat() *big.Float {
	newfloat := big.NewFloat(0)
	newfloat.SetInt(this.Val)
	return newfloat
}

func (this *Integer) AddI(i *Integer) {
	this.Val.Add(this.Val, i.Val)
	this.cachedHash = 0
}

func (this *Integer) MulI(i *Integer) {
	this.Val.Mul(this.Val, i.Val)
	this.cachedHash = 0
}
