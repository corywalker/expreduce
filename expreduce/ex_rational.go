package expreduce

import "fmt"
import "math/big"

type Rational struct {
	Num *big.Int
	Den *big.Int
}

func (this *Rational) Eval(es *EvalState) Ex {
	if this.Num.Cmp(big.NewInt(0)) == 0 && this.Den.Cmp(big.NewInt(0)) == 0 {
		return &Symbol{"Indeterminate"}
	}
	if this.Den.Cmp(big.NewInt(0)) == 0 {
		return &Symbol{"ComplexInfinity"}
	}
	if this.Num.Cmp(big.NewInt(0)) == 0 {
		return &Integer{big.NewInt(0)}
	}
	negNum := this.Num.Cmp(big.NewInt(0)) == -1
	negDen := this.Den.Cmp(big.NewInt(0)) == -1
	negateRes := negNum != negDen
	absNum := big.NewInt(0)
	absNum.Abs(this.Num)
	absDen := big.NewInt(0)
	absDen.Abs(this.Den)

	gcd := big.NewInt(0)
	gcd.GCD(nil, nil, absNum, absDen)
	absNum.Div(absNum, gcd)
	absDen.Div(absDen, gcd)

	if absDen.Cmp(big.NewInt(1)) == 0 {
		if !negateRes {
			return &Integer{absNum}
		} else {
			return &Integer{absNum.Neg(absNum)}
		}
	}

	if !negateRes {
		this.Num.Set(absNum)
		this.Den.Set(absDen)
		return this
	} else {
		this.Num.Set(absNum.Neg(absNum))
		this.Den.Set(absDen)
		return this
	}
	return this
}

func (this *Rational) StringForm(form string) string {
	return fmt.Sprintf("%d/%d", this.Num, this.Den)
}

func (this *Rational) String() string {
	return this.StringForm("InputForm")
}

func (this *Rational) IsEqual(other Ex, cl *CASLogger) string {
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

func (this *Rational) DeepCopy() Ex {
	tmpn := big.NewInt(0)
	tmpn.Set(this.Num)
	tmpd := big.NewInt(0)
	tmpd.Set(this.Den)
	return &Rational{tmpn, tmpd}
}

func (this *Rational) AsBigRat() *big.Rat {
	return big.NewRat(this.Num.Int64(), this.Den.Int64())
}

