package cas

import "fmt"

// Floating point numbers represented by float64
type Float struct {
	Val float64
}

func (f *Float) Eval() Ex {
	return f
}

func (f *Float) ToString() string {
	return fmt.Sprintf("%g", f.Val)
}

func (this *Float) IsEqual(other Ex) string {
	otherConv, ok := other.(*Float)
	if !ok {
		return "EQUAL_FALSE"
	}
	if this.Val != otherConv.Val {
		return "EQUAL_FALSE"
	}
	return "EQUAL_TRUE"
}
