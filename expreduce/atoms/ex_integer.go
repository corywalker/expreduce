package atoms

import (
	"fmt"
	"hash/fnv"
	"math/big"

	"github.com/corywalker/expreduce/expreduce/parser/parens"
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

func (i *Integer) StringForm(params expreduceapi.ToStringParams) string {
	if i.Val.Cmp(big.NewInt(0)) < 0 {
		if parens.NeedsParens("System`Times", params.PreviousHead) {
			if params.Form == "TeXForm" {
				return fmt.Sprintf("{(%d)}", i.Val)
			}
			return fmt.Sprintf("(%d)", i.Val)
		}
	}
	return fmt.Sprintf("%d", i.Val)
}

func (this *Integer) String(esi expreduceapi.EvalStateInterface) string {
	context, contextPath := defaultStringFormArgs()
	return this.StringForm(expreduceapi.ToStringParams{Form: "InputForm", Context: context, ContextPath: contextPath, Esi: esi})
}

func (this *Integer) IsEqual(other expreduceapi.Ex) string {
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

func (this *Integer) DeepCopy() expreduceapi.Ex {
	tmp := big.NewInt(0)
	tmp.Set(this.Val)
	return &Integer{Val: tmp, cachedHash: this.cachedHash}
}

func (this *Integer) Copy() expreduceapi.Ex {
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

func (this *Integer) asBigFloat() *big.Float {
	newfloat := big.NewFloat(0)
	newfloat.SetInt(this.Val)
	return newfloat
}

func (this *Integer) addI(i *Integer) {
	this.Val.Add(this.Val, i.Val)
	this.cachedHash = 0
}

func (this *Integer) mulI(i *Integer) {
	this.Val.Mul(this.Val, i.Val)
	this.cachedHash = 0
}
