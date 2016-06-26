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

func (this *Flt) Replace(r *Rule, es *EvalState) Ex {
	if this.IsMatchQ(r.Lhs, es) {
		return r.Rhs
	}
	return this
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
		otherInteger, ok := other.(*Integer)
		if ok {
			otherAsFlt := big.NewFloat(0)
			otherAsFlt.SetInt(otherInteger.Val)
			if otherAsFlt.Cmp(this.Val) == 0 {
				return "EQUAL_TRUE"
			}
		}
		return "EQUAL_FALSE"
	}
	if this.Val.Cmp(otherConv.Val) != 0 {
		return "EQUAL_FALSE"
	}
	return "EQUAL_TRUE"
}

func (this *Flt) IsSameQ(other Ex, es *EvalState) bool {
	_, ok := other.(*Flt)
	if !ok {
		return false
	}
	return this.IsEqual(other, es) == "EQUAL_TRUE"
}

func (this *Flt) IsMatchQ(otherEx Ex, es *EvalState) bool {
	return this.IsSameQ(otherEx, es)
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

func (this *Integer) Replace(r *Rule, es *EvalState) Ex {
	if this.IsMatchQ(r.Lhs, es) {
		return r.Rhs
	}
	return this
}

func (f *Integer) ToString() string {
	return fmt.Sprintf("%d", f.Val)
}

func (this *Integer) IsEqual(other Ex, es *EvalState) string {
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
		return "EQUAL_FALSE"
	}
	if this.Val.Cmp(otherConv.Val) != 0 {
		return "EQUAL_FALSE"
	}
	return "EQUAL_TRUE"
}

func (this *Integer) IsSameQ(other Ex, es *EvalState) bool {
	_, ok := other.(*Integer)
	if !ok {
		return false
	}
	return this.IsEqual(other, es) == "EQUAL_TRUE"
}

func (this *Integer) IsMatchQ(otherEx Ex, es *EvalState) bool {
	return this.IsSameQ(otherEx, es)
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

func (this *Error) Replace(r *Rule, es *EvalState) Ex {
	if this.IsMatchQ(r.Lhs, es) {
		return r.Rhs
	}
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

func (this *Error) IsSameQ(other Ex, es *EvalState) bool {
	_, ok := other.(*Error)
	if !ok {
		return false
	}
	return this.IsEqual(other, es) == "EQUAL_TRUE"
}

func (this *Error) IsMatchQ(otherEx Ex, es *EvalState) bool {
	return this.IsSameQ(otherEx, es)
}

func (this *Error) DeepCopy() Ex {
	thiscopy := *this
	return &thiscopy
}
