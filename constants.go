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

func (this *Flt) Replace(r *Expression, es *EvalState) Ex {
	if IsMatchQ(this, r.Parts[1], es) {
		return r.Parts[2]
	}
	return this
}

func (f *Flt) String() string {
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
		return "EQUAL_UNK"
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
	if IsBlankTypeCapturing(otherEx, this, "Real", es) {
		return true
	}
	return this.IsSameQ(otherEx, es)
}

func (this *Flt) DeepCopy() Ex {
	tmp := big.NewFloat(0)
	tmp.Copy(this.Val)
	return &Flt{tmp}
}

func IntegerToFlt(i *Integer) (*Flt, bool) {
	newfloat := big.NewFloat(0)
	newfloat.SetInt(i.Val)
	return &Flt{newfloat}, true
}

// Integer numbers represented by big.Int
type Integer struct {
	Val *big.Int
}

func (f *Integer) Eval(es *EvalState) Ex {
	return f
}

func (this *Integer) Replace(r *Expression, es *EvalState) Ex {
	if IsMatchQ(this, r.Parts[1], es) {
		return r.Parts[2]
	}
	return this
}

func (f *Integer) String() string {
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
		return "EQUAL_UNK"
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
	if IsBlankTypeCapturing(otherEx, this, "Integer", es) {
		return true
	}
	return this.IsSameQ(otherEx, es)
}

func (this *Integer) DeepCopy() Ex {
	tmp := big.NewInt(0)
	tmp.Set(this.Val)
	return &Integer{tmp}
}

type String struct {
	Val string
}

func (this *String) Eval(es *EvalState) Ex {
	return this
}

func (this *String) Replace(r *Expression, es *EvalState) Ex {
	if IsMatchQ(this, r.Parts[1], es) {
		return r.Parts[2]
	}
	return this
}

func (this *String) String() string {
	return fmt.Sprintf("\"%v\"", this.Val)
}

func (this *String) IsEqual(other Ex, es *EvalState) string {
	otherConv, ok := other.(*String)
	if !ok {
		return "EQUAL_FALSE"
	}
	if this.Val != otherConv.Val {
		return "EQUAL_FALSE"
	}
	return "EQUAL_TRUE"
}

func (this *String) IsSameQ(other Ex, es *EvalState) bool {
	_, ok := other.(*String)
	if !ok {
		return false
	}
	return this.IsEqual(other, es) == "EQUAL_TRUE"
}

func (this *String) IsMatchQ(otherEx Ex, es *EvalState) bool {
	if IsBlankTypeCapturing(otherEx, this, "String", es) {
		return true
	}
	return this.IsSameQ(otherEx, es)
}

func (this *String) DeepCopy() Ex {
	thiscopy := *this
	return &thiscopy
}
