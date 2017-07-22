package expreduce

import "fmt"
import "hash/fnv"

type String struct {
	Val string
}

func (this *String) Eval(es *EvalState) Ex {
	return this
}

func (this *String) StringForm(form string, context *String, contextPath *Expression) string {
	if form == "OutputForm" {
		return fmt.Sprintf("%v", this.Val)
	}
	return fmt.Sprintf("\"%v\"", this.Val)
}

func (this *String) String() string {
	context, contextPath := DefaultStringFormArgs()
	return this.StringForm("InputForm", context, contextPath)
}

func (this *String) IsEqual(other Ex, cl *CASLogger) string {
	otherConv, ok := other.(*String)
	if !ok {
		return "EQUAL_FALSE"
	}
	if this.Val != otherConv.Val {
		return "EQUAL_FALSE"
	}
	return "EQUAL_TRUE"
}

func (this *String) DeepCopy() Ex {
	thiscopy := *this
	return &thiscopy
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
