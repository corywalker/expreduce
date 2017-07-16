package expreduce

import "fmt"
import "math/big"
import "bytes"
import "hash"

// Floating point numbers represented by big.Float
type Flt struct {
	Val *big.Float
}

func (f *Flt) Eval(es *EvalState) Ex {
	return f
}

func (f *Flt) StringForm(form string) string {
	var buffer bytes.Buffer
	buffer.WriteString(fmt.Sprintf("%.6g", f.Val))
	if bytes.IndexRune(buffer.Bytes(), '.') == -1 {
		buffer.WriteString(".")
	}
	return buffer.String()
}

func (this *Flt) String() string {
	return this.StringForm("InputForm")
}

func (this *Flt) IsEqual(other Ex, cl *CASLogger) string {
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

func RationalToFlt(r *Rational) (*Flt, bool) {
	newfloat := big.NewFloat(0)
	newfloat.SetRat(r.AsBigRat())
	return &Flt{newfloat}, true
}

func (this *Flt) NeedsEval() bool {
	return false
}

func (this *Flt) Hash(h *hash.Hash64) {
	(*h).Write([]byte{195, 244, 76, 249, 227, 115, 88, 251})
	bytes, _ := this.Val.MarshalText()
	(*h).Write(bytes)
}

func (this *Flt) AddI(i *Integer) {
	this.Val.Add(this.Val, i.AsBigFloat())
}

func (this *Flt) AddR(r *Rational) {
	this.Val.Add(this.Val, r.AsBigFloat())
}

func (this *Flt) AddF(f *Flt) {
	this.Val.Add(this.Val, f.Val)
}
