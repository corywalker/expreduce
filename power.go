package cas

import (
	"bytes"
	"github.com/corywalker/mathbigext"
	"math/big"
)

func (this *Expression) EvalPower(es *EvalState) Ex {
	if len(this.Parts) != 3 {
		return this
	}

	// TODO: Handle cases like float raised to the float and things raised to
	// zero and 1

	baseInt, baseIsInt := this.Parts[1].(*Integer)
	powerInt, powerIsInt := this.Parts[2].(*Integer)
	baseFlt, baseIsFlt := this.Parts[1].(*Flt)
	powerFlt, powerIsFlt := this.Parts[2].(*Flt)
	// Anything raised to the 1st power is itself
	if powerIsFlt {
		if powerFlt.Val.Cmp(big.NewFloat(1)) == 0 {
			return this.Parts[1]
		}
	} else if powerIsInt {
		if powerInt.Val.Cmp(big.NewInt(1)) == 0 {
			return this.Parts[1]
		}
	}
	// Anything raised to the 0th power is 1, with a small exception
	isZerothPower := false
	if powerIsFlt {
		if powerFlt.Val.Cmp(big.NewFloat(0)) == 0 {
			isZerothPower = true
		}
	} else if powerIsInt {
		if powerInt.Val.Cmp(big.NewInt(0)) == 0 {
			isZerothPower = true
		}
	}
	isZeroBase := false
	if baseIsFlt {
		if baseFlt.Val.Cmp(big.NewFloat(0)) == 0 {
			isZeroBase = true
		}
	} else if baseIsInt {
		if baseInt.Val.Cmp(big.NewInt(0)) == 0 {
			isZeroBase = true
		}
	}
	if isZerothPower {
		if isZeroBase {
			return &Symbol{"Indeterminate"}
		}
		return &Integer{big.NewInt(1)}
	}

	//es.Debugf("Power eval. baseIsInt=%v, powerIsInt=%v", baseIsInt, powerIsInt)
	// Fully integer Power expression
	if baseIsInt && powerIsInt {
		cmpres := powerInt.Val.Cmp(big.NewInt(0))
		//es.Debugf("Cmpres: %v", cmpres)
		if cmpres == 1 {
			res := big.NewInt(0)
			res.Exp(baseInt.Val, powerInt.Val, nil)
			return &Integer{res}
		} else if cmpres == -1 {
			newbase := big.NewInt(0)
			absPower := big.NewInt(0)
			absPower.Abs(powerInt.Val)
			newbase.Exp(baseInt.Val, absPower, nil)
			if newbase.Cmp(big.NewInt(1)) == 0 {
				return &Integer{big.NewInt(1)}
			}
			if newbase.Cmp(big.NewInt(-1)) == 0 {
				return &Integer{big.NewInt(-1)}
			}
			return &Expression{[]Ex{&Symbol{"Power"}, &Integer{newbase}, &Integer{big.NewInt(-1)}}}
			//return &Expression{[]Ex{&Symbol{"Rational"}, &Integer{big.NewInt(1)}, &Integer{newbase}}}
		} else {
			return &Expression{[]Ex{&Symbol{"Error"}, &String{"Unexpected zero power in Power evaluation."}}}
		}
	}

	if baseIsFlt && powerIsInt {
		return &Flt{mathbigext.Pow(baseFlt.Val, big.NewFloat(0).SetInt(powerInt.Val))}
	}
	if baseIsInt && powerIsFlt {
		return &Flt{mathbigext.Pow(big.NewFloat(0).SetInt(baseInt.Val), powerFlt.Val)}
	}
	if baseIsFlt && powerIsFlt {
		return &Flt{mathbigext.Pow(baseFlt.Val, powerFlt.Val)}
	}

	return this
}

func (this *Expression) ToStringPower() string {
	var buffer bytes.Buffer
	buffer.WriteString(this.Parts[1].String())
	buffer.WriteString("^")
	buffer.WriteString(this.Parts[2].String())
	return buffer.String()
}
