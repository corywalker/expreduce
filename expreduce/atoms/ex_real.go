package atoms

import (
	"bytes"
	"fmt"
	"hash/fnv"
	"math/big"
	"strings"

	"github.com/corywalker/expreduce/expreduce/parser/parens"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

// Floating point numbers represented by big.Float
type Flt struct {
	Val *big.Float
}

func (f *Flt) StringForm(params expreduceapi.ToStringParams) string {
	var buffer bytes.Buffer
	useParens := false
	if f.Val.Cmp(big.NewFloat(0)) < 0 {
		if parens.NeedsParens("System`Times", params.PreviousHead) {
			useParens = true
			if params.Form == "TeXForm" {
				buffer.WriteString("{")
			}
			buffer.WriteString("(")
		}
	}
	buffer.WriteString(fmt.Sprintf("%.6g", f.Val))
	if bytes.IndexRune(buffer.Bytes(), '.') == -1 {
		buffer.WriteString(".")
	}
	if useParens {
		buffer.WriteString(")")
		if params.Form == "TeXForm" {
			buffer.WriteString("}")
		}
	}
	return buffer.String()
}

func (this *Flt) String(esi expreduceapi.EvalStateInterface) string {
	context, contextPath := defaultStringFormArgs()
	return this.StringForm(expreduceapi.ToStringParams{Form: "InputForm", Context: context, ContextPath: contextPath, Esi: esi})
}

func (this *Flt) IsEqual(other expreduceapi.Ex) string {
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
	thisStr := fmt.Sprintf("%.14g", this.Val)
	otherStr := fmt.Sprintf("%.14g", otherConv.Val)
	if strings.Compare(thisStr, otherStr) != 0 {
		return "EQUAL_FALSE"
	}
	return "EQUAL_TRUE"
}

func (this *Flt) DeepCopy() expreduceapi.Ex {
	tmp := big.NewFloat(0)
	tmp.Copy(this.Val)
	return NewReal(tmp)
}

func (this *Flt) Copy() expreduceapi.Ex {
	return this.DeepCopy()
}

func IntegerToFlt(i *Integer) (*Flt, bool) {
	newfloat := big.NewFloat(0)
	newfloat.SetInt(i.Val)
	return NewReal(newfloat), true
}

func RationalToFlt(r *Rational) (*Flt, bool) {
	newfloat := big.NewFloat(0)
	newfloat.SetRat(r.asBigRat())
	return NewReal(newfloat), true
}

func (this *Flt) NeedsEval() bool {
	return false
}

func (this *Flt) Hash() uint64 {
	h := fnv.New64a()
	h.Write([]byte{195, 244, 76, 249, 227, 115, 88, 251})
	bytes, _ := this.Val.MarshalText()
	h.Write(bytes)
	return h.Sum64()
}

func (this *Flt) addI(i *Integer) {
	this.Val.Add(this.Val, i.asBigFloat())
}

func (this *Flt) addR(r *Rational) {
	this.Val.Add(this.Val, r.asBigFloat())
}

func (this *Flt) addF(f *Flt) {
	this.Val.Add(this.Val, f.Val)
}

func (this *Flt) mulI(i *Integer) {
	this.Val.Mul(this.Val, i.asBigFloat())
}

func (this *Flt) mulR(r *Rational) {
	this.Val.Mul(this.Val, r.asBigFloat())
}

func (this *Flt) mulF(f *Flt) {
	this.Val.Mul(this.Val, f.Val)
}

func NewReal(v *big.Float) *Flt {
	return &Flt{v}
}
