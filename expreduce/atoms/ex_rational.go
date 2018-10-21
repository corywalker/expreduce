package atoms

import (
	"fmt"
	"hash/fnv"
	"math/big"

	"github.com/corywalker/expreduce/expreduce/parser"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

type Rational struct {
	Num       *big.Int
	Den       *big.Int
	needsEval bool
}

func (this *Rational) StringForm(params expreduceapi.ToStringParams) string {
	if params.Form == "FullForm" {
		return fmt.Sprintf("Rational[%d, %d]", this.Num, this.Den)
	}
	if params.Form == "TeXForm" {
		return fmt.Sprintf("\\frac{%d}{%d}", this.Num, this.Den)
	}
	if parser.NeedsParens("System`Times", params.PreviousHead) {
		return fmt.Sprintf("(%d/%d)", this.Num, this.Den)
	}
	return fmt.Sprintf("%d/%d", this.Num, this.Den)
}

func (this *Rational) String(esi expreduceapi.EvalStateInterface) string {
	context, ContextPath := DefaultStringFormArgs()
	return this.StringForm(expreduceapi.ToStringParams{Form: "InputForm", Context: context, ContextPath: ContextPath, Esi: esi})
}

func (this *Rational) IsEqual(other expreduceapi.Ex) string {
	otherConv, otherIsRational := other.(*Rational)
	if !otherIsRational {
		return "EQUAL_FALSE"
	}
	// Assume rational already simplified
	if (this.Num.Cmp(otherConv.Num) != 0) || (this.Den.Cmp(otherConv.Den) != 0) {
		return "EQUAL_FALSE"
	}
	return "EQUAL_TRUE"
}

func (this *Rational) DeepCopy() expreduceapi.Ex {
	tmpn := big.NewInt(0)
	tmpn.Set(this.Num)
	tmpd := big.NewInt(0)
	tmpd.Set(this.Den)
	return &Rational{tmpn, tmpd, this.needsEval}
}

func (this *Rational) Copy() expreduceapi.Ex {
	return this.DeepCopy()
}

func (this *Rational) AsBigRat() *big.Rat {
	res := big.NewRat(1, 1)
	return res.SetFrac(this.Num, this.Den)
}

func (this *Rational) NeedsEval() bool {
	return this.needsEval
}

func NewRational(n *big.Int, d *big.Int) *Rational {
	return &Rational{n, d, true}
}

func (this *Rational) Hash() uint64 {
	h := fnv.New64a()
	h.Write([]byte{90, 82, 214, 51, 52, 7, 7, 33})
	nBytes, _ := this.Num.MarshalText()
	h.Write(nBytes)
	dBytes, _ := this.Den.MarshalText()
	h.Write(dBytes)
	return h.Sum64()
}

func (this *Rational) AsBigFloat() *big.Float {
	num := big.NewFloat(0)
	den := big.NewFloat(0)
	newquo := big.NewFloat(0)
	num.SetInt(this.Num)
	den.SetInt(this.Den)
	newquo.Quo(num, den)
	return newquo
}

func (this *Rational) AddI(i *Integer) {
	tmp := big.NewInt(0)
	tmp.Mul(i.Val, this.Den)
	this.Num.Add(this.Num, tmp)
}

func (this *Rational) AddR(r *Rational) {
	tmp := big.NewInt(0)
	// lastrNum/lastrDen + theratNum/theratDen // Together
	tmp.Mul(this.Den, r.Num)
	this.Den.Mul(this.Den, r.Den)
	this.Num.Mul(this.Num, r.Den)
	this.Num.Add(this.Num, tmp)
}

func (this *Rational) MulI(i *Integer) {
	this.Num.Mul(this.Num, i.Val)
}

func (this *Rational) MulBigI(i *big.Int) {
	this.Num.Mul(this.Num, i)
}

func (this *Rational) MulR(r *Rational) {
	this.Num.Mul(this.Num, r.Num)
	this.Den.Mul(this.Den, r.Den)
}
