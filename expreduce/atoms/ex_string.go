package atoms

import (
	"fmt"
	"hash/fnv"

	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

type String struct {
	Val string
}

func (this *String) StringForm(params expreduceapi.ToStringParams) string {
	if params.Form == "OutputForm" ||
		params.Form == "TraditionalForm" ||
		params.Form == "StandardForm" {
		return fmt.Sprintf("%v", this.Val)
	}
	return fmt.Sprintf("\"%v\"", this.Val)
}

func (this *String) String(esi expreduceapi.EvalStateInterface) string {
	context, ContextPath := DefaultStringFormArgs()
	return this.StringForm(expreduceapi.ToStringParams{Form: "InputForm", Context: context, ContextPath: ContextPath, Esi: esi})
}

func (this *String) IsEqual(other expreduceapi.Ex) string {
	otherConv, ok := other.(*String)
	if !ok {
		return "EQUAL_FALSE"
	}
	if this.Val != otherConv.Val {
		return "EQUAL_FALSE"
	}
	return "EQUAL_TRUE"
}

func (this *String) DeepCopy() expreduceapi.Ex {
	thiscopy := *this
	return &thiscopy
}

func (this *String) Copy() expreduceapi.Ex {
	return this.DeepCopy()
}

func (this *String) NeedsEval() bool {
	return false
}

func (this *String) GetValue() string {
	return this.Val
}

func (this *String) Hash() uint64 {
	h := fnv.New64a()
	h.Write([]byte{102, 206, 57, 172, 207, 100, 198, 133})
	h.Write([]byte(this.Val))
	return h.Sum64()
}

func NewString(v string) *String {
	return &String{v}
}
