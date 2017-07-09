package expreduce

import "fmt"
import "math/big"

// Integer numbers represented by big.Int
type Integer struct {
	Val *big.Int
}

func (f *Integer) Eval(es *EvalState) Ex {
	return f
}

func (f *Integer) StringForm(form string) string {
	return fmt.Sprintf("%d", f.Val)
}

func (this *Integer) String() string {
	return this.StringForm("InputForm")
}

func (this *Integer) IsEqual(other Ex, cl *CASLogger) string {
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
	return &Integer{tmp}
}

func (this *Integer) NeedsEval() bool {
	return false
}

func NewInt(i int64) *Integer {
	return &Integer{big.NewInt(i)}
}
