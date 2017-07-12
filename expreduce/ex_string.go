package expreduce

import "fmt"

type String struct {
	Val string
}

func (this *String) Eval(es *EvalState) Ex {
	return this
}

func (this *String) StringForm(form string) string {
	if form == "OutputForm" {
		return fmt.Sprintf("%v", this.Val)
	}
	return fmt.Sprintf("\"%v\"", this.Val)
}

func (this *String) String() string {
	return this.StringForm("InputForm")
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
