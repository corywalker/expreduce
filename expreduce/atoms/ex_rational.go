package atoms

import (
	"fmt"
	"hash/fnv"
	"math/big"

	"github.com/corywalker/expreduce/expreduce/parser/parens"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

type Rational struct {
	Num       *big.Int
	Den       *big.Int
	needsEval bool
}

func (thisRational *Rational) StringForm(
	params expreduceapi.ToStringParams,
) string {
	if params.Form == "FullForm" {
		return fmt.Sprintf(
			"Rational[%d, %d]",
			thisRational.Num,
			thisRational.Den,
		)
	}
	if params.Form == "TeXForm" {
		return fmt.Sprintf("\\frac{%d}{%d}", thisRational.Num, thisRational.Den)
	}
	if parens.NeedsParens("System`Times", params.PreviousHead) {
		return fmt.Sprintf("(%d/%d)", thisRational.Num, thisRational.Den)
	}
	return fmt.Sprintf("%d/%d", thisRational.Num, thisRational.Den)
}

func (thisRational *Rational) IsEqual(other expreduceapi.Ex) string {
	otherConv, otherIsRational := other.(*Rational)
	if !otherIsRational {
		return "EQUAL_FALSE"
	}
	// Assume rational already simplified
	if (thisRational.Num.Cmp(otherConv.Num) != 0) ||
		(thisRational.Den.Cmp(otherConv.Den) != 0) {
		return "EQUAL_FALSE"
	}
	return "EQUAL_TRUE"
}

func (thisRational *Rational) DeepCopy() expreduceapi.Ex {
	tmpn := big.NewInt(0)
	tmpn.Set(thisRational.Num)
	tmpd := big.NewInt(0)
	tmpd.Set(thisRational.Den)
	return &Rational{tmpn, tmpd, thisRational.needsEval}
}

func (thisRational *Rational) Copy() expreduceapi.Ex {
	return thisRational.DeepCopy()
}

func (thisRational *Rational) asBigRat() *big.Rat {
	res := big.NewRat(1, 1)
	return res.SetFrac(thisRational.Num, thisRational.Den)
}

func (thisRational *Rational) NeedsEval() bool {
	return thisRational.needsEval
}

func (thisRational *Rational) SetNeedsEval(newVal bool) {
	thisRational.needsEval = newVal
}

func NewRational(n *big.Int, d *big.Int) *Rational {
	return &Rational{n, d, true}
}

func (thisRational *Rational) Hash() uint64 {
	h := fnv.New64a()
	h.Write([]byte{90, 82, 214, 51, 52, 7, 7, 33})
	nBytes, _ := thisRational.Num.GobEncode()
	h.Write(nBytes)
	dBytes, _ := thisRational.Den.GobEncode()
	h.Write(dBytes)
	return h.Sum64()
}

func (thisRational *Rational) asBigFloat() *big.Float {
	num := big.NewFloat(0)
	den := big.NewFloat(0)
	newquo := big.NewFloat(0)
	num.SetInt(thisRational.Num)
	den.SetInt(thisRational.Den)
	newquo.Quo(num, den)
	return newquo
}

func (thisRational *Rational) addI(i *Integer) {
	tmp := big.NewInt(0)
	tmp.Mul(i.Val, thisRational.Den)
	thisRational.Num.Add(thisRational.Num, tmp)
}

func (thisRational *Rational) addR(otherR *Rational) {
	tmp := big.NewInt(0)
	// lastrNum/lastrDen + theratNum/theratDen // Together
	tmp.Mul(thisRational.Den, otherR.Num)
	thisRational.Den.Mul(thisRational.Den, otherR.Den)
	thisRational.Num.Mul(thisRational.Num, otherR.Den)
	thisRational.Num.Add(thisRational.Num, tmp)
}

func (thisRational *Rational) mulI(i *Integer) {
	thisRational.Num.Mul(thisRational.Num, i.Val)
}

func (thisRational *Rational) MulBigI(i *big.Int) {
	thisRational.Num.Mul(thisRational.Num, i)
}

func (thisRational *Rational) mulR(otherR *Rational) {
	thisRational.Num.Mul(thisRational.Num, otherR.Num)
	thisRational.Den.Mul(thisRational.Den, otherR.Den)
}
