package expreduce

import (
	"fmt"
	"hash/fnv"

	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

type String struct {
	Val string
}

func (this *String) Eval(es expreduceapi.EvalStateInterface) expreduceapi.Ex {
	return this
}

func (this *String) StringForm(params expreduceapi.ToStringParams) string {
	if params.form == "OutputForm" ||
		params.form == "TraditionalForm" ||
		params.form == "StandardForm" {
		return fmt.Sprintf("%v", this.Val)
	}
	return fmt.Sprintf("\"%v\"", this.Val)
}

func (this *String) String(esi expreduceapi.EvalStateInterface) string {
	context, contextPath := DefaultStringFormArgs()
	return this.StringForm(expreduceapi.ToStringParams{form: "InputForm", context: context, contextPath: contextPath, esi: esi})
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

func (this *String) Hash() uint64 {
	h := fnv.New64a()
	h.Write([]byte{102, 206, 57, 172, 207, 100, 198, 133})
	h.Write([]byte(this.Val))
	return h.Sum64()
}

func NewString(v string) *String {
	return &String{v}
}
