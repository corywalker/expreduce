package cas

import "fmt"
import "math/big"

// Floating point numbers represented by big.Float
type Flt struct {
	Val *big.Float
}

func (f *Flt) Eval() Ex {
	return f
}

func (f *Flt) ToString() string {
	return fmt.Sprintf("%g", f.Val)
}

func (this *Flt) IsEqual(other Ex) string {
	otherConv, ok := other.(*Flt)
	if !ok {
		return "EQUAL_FALSE"
	}
	if this.Val.Cmp(otherConv.Val) != 0 {
		return "EQUAL_FALSE"
	}
	return "EQUAL_TRUE"
}

type Bool struct {
	Val bool
}

func (this *Bool) Eval() Ex {
	return this
}

func (this *Bool) ToString() string {
	return fmt.Sprintf("%v", this.Val)
}

func (this *Bool) IsEqual(other Ex) string {
	otherConv, ok := other.(*Bool)
	if !ok {
		return "EQUAL_FALSE"
	}
	if this.Val != otherConv.Val {
		return "EQUAL_FALSE"
	}
	return "EQUAL_TRUE"
}

type Error struct {
	Val string
}

func (this *Error) Eval() Ex {
	return this
}

func (this *Error) ToString() string {
	return fmt.Sprintf("%v", this.Val)
}

func (this *Error) IsEqual(other Ex) string {
	otherConv, ok := other.(*Error)
	if !ok {
		return "EQUAL_FALSE"
	}
	if this.Val != otherConv.Val {
		return "EQUAL_FALSE"
	}
	return "EQUAL_TRUE"
}
