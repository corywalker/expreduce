package atoms

import (
	"fmt"
	"hash/fnv"

	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

type String struct {
	Val string
}

func (str *String) StringForm(params expreduceapi.ToStringParams) string {
	if params.Form == "OutputForm" ||
		params.Form == "TraditionalForm" ||
		params.Form == "StandardForm" {
		return fmt.Sprintf("%v", str.Val)
	}
	return fmt.Sprintf("\"%v\"", str.Val)
}

func (str *String) String(esi expreduceapi.EvalStateInterface) string {
	context, contextPath := defaultStringFormArgs()
	return str.StringForm(expreduceapi.ToStringParams{Form: "InputForm", Context: context, ContextPath: contextPath, Esi: esi})
}

func (str *String) IsEqual(other expreduceapi.Ex) string {
	otherConv, ok := other.(*String)
	if !ok {
		return "EQUAL_FALSE"
	}
	if str.Val != otherConv.Val {
		return "EQUAL_FALSE"
	}
	return "EQUAL_TRUE"
}

func (str *String) DeepCopy() expreduceapi.Ex {
	strcopy := *str
	return &strcopy
}

func (str *String) Copy() expreduceapi.Ex {
	return str.DeepCopy()
}

func (str *String) NeedsEval() bool {
	return false
}

func (str *String) GetValue() string {
	return str.Val
}

func (str *String) Hash() uint64 {
	h := fnv.New64a()
	h.Write([]byte{102, 206, 57, 172, 207, 100, 198, 133})
	h.Write([]byte(str.Val))
	return h.Sum64()
}

func NewString(v string) *String {
	return &String{v}
}
