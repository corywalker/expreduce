package cas

import "fmt"
import "math/big"
import "bytes"

// Floating point numbers represented by big.Float
type Flt struct {
	Val *big.Float
}

func (f *Flt) Eval(es *EvalState) Ex {
	return f
}

func (f *Flt) ToString() string {
	var buffer bytes.Buffer
	buffer.WriteString(fmt.Sprintf("%g", f.Val))
	if bytes.IndexRune(buffer.Bytes(), '.') == -1 {
		buffer.WriteString(".")
	}
	return buffer.String()
}

func (this *Flt) IsEqual(other Ex, es *EvalState) string {
	otherConv, ok := other.(*Flt)
	if !ok {
		return "EQUAL_FALSE"
	}
	if this.Val.Cmp(otherConv.Val) != 0 {
		return "EQUAL_FALSE"
	}
	return "EQUAL_TRUE"
}

func (this *Flt) DeepCopy() Ex {
	tmp := big.NewFloat(0)
	tmp.Copy(this.Val)
	return &Flt{tmp}
}

// Integer numbers represented by big.Int
type Integer struct {
	Val *big.Int
}

func (f *Integer) Eval(es *EvalState) Ex {
	return f
}

func (f *Integer) ToString() string {
	return fmt.Sprintf("%d", f.Val)
}

func (this *Integer) IsEqual(other Ex, es *EvalState) string {
	otherConv, ok := other.(*Integer)
	if !ok {
		return "EQUAL_FALSE"
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

type Error struct {
	Val string
}

func (this *Error) Eval(es *EvalState) Ex {
	return this
}

func (this *Error) ToString() string {
	return fmt.Sprintf("%v", this.Val)
}

func (this *Error) IsEqual(other Ex, es *EvalState) string {
	otherConv, ok := other.(*Error)
	if !ok {
		return "EQUAL_FALSE"
	}
	if this.Val != otherConv.Val {
		return "EQUAL_FALSE"
	}
	return "EQUAL_TRUE"
}

func (this *Error) DeepCopy() Ex {
	thiscopy := *this
	return &thiscopy
}
