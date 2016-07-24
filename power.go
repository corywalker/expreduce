package cas

import (
	"bytes"
	"github.com/corywalker/mathbigext"
	"math/big"
	//"fmt"
)

// An exponent expression with a base and an exponent
type Power struct {
	Base  Ex
	Power Ex
}

func (this *Power) Eval(es *EvalState) Ex {
	// Start by evaluating each part
	this.Base = this.Base.Eval(es)
	this.Power = this.Power.Eval(es)

	// TODO: Handle cases like float raised to the float and things raised to
	// zero and 1

	baseInt, baseIsInt := this.Base.(*Integer)
	powerInt, powerIsInt := this.Power.(*Integer)
	baseFlt, baseIsFlt := this.Base.(*Flt)
	powerFlt, powerIsFlt := this.Power.(*Flt)
	// Anything raised to the 1st power is itself
	if powerIsFlt {
		if powerFlt.Val.Cmp(big.NewFloat(1)) == 0 {
			return this.Base
		}
	} else if powerIsInt {
		if powerInt.Val.Cmp(big.NewInt(1)) == 0 {
			return this.Base
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

	//es.log.Debugf(es.Pre() + "Power eval. baseIsInt=%v, powerIsInt=%v", baseIsInt, powerIsInt)
	// Fully integer Power expression
	if baseIsInt && powerIsInt {
		cmpres := powerInt.Val.Cmp(big.NewInt(0))
		//es.log.Debugf(es.Pre() + "Cmpres: %v", cmpres)
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
			return &Power{&Integer{newbase}, &Integer{big.NewInt(-1)}}
		} else {
			return &Error{"Unexpected zero power in Power evaluation."}
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

func (this *Power) Replace(r *Rule, es *EvalState) Ex {
	if this.IsMatchQ(r.Lhs, es) {
		return r.Rhs
	}
	this.Base = this.Base.Replace(r, es)
	this.Power = this.Power.Replace(r, es)
	return this.Eval(es)
}

func (this *Power) ToString() string {
	var buffer bytes.Buffer
	buffer.WriteString(this.Base.ToString())
	buffer.WriteString("^")
	buffer.WriteString(this.Power.ToString())
	return buffer.String()
}

func (this *Power) IsEqual(otherEx Ex, es *EvalState) string {
	thisEx := this.Eval(es)
	otherEx = otherEx.Eval(es)
	this, ok := thisEx.(*Power)
	if !ok {
		return thisEx.IsEqual(otherEx, es)
	}
	other, ok := otherEx.(*Power)
	if !ok {
		return "EQUAL_UNK"
	}
	// TODO: Could be improved by knowing about base conversions and logarithms
	var baseEqual = this.Base.IsEqual(other.Base, es) == "EQUAL_TRUE"
	var exponentEqual = this.Power.IsEqual(other.Power, es) == "EQUAL_TRUE"

	if baseEqual && exponentEqual {
		return "EQUAL_TRUE"
	}
	return "EQUAL_UNK"
}

func (this *Power) IsSameQ(otherEx Ex, es *EvalState) bool {
	thisEx := this.Eval(es)
	otherEx = otherEx.Eval(es)
	this, ok := thisEx.(*Power)
	if !ok {
		return thisEx.IsSameQ(otherEx, es)
	}
	other, ok := otherEx.(*Power)
	if !ok {
		return false
	}
	var baseSame = this.Base.IsMatchQ(other.Base, es)
	var exponentSame = this.Power.IsMatchQ(other.Power, es)

	if baseSame && exponentSame {
		return true
	}
	return false
}

func (this *Power) IsMatchQ(otherEx Ex, es *EvalState) bool {
	if IsBlankTypeCapturing(otherEx, this, "Power", es) {
		return true
	}
	return this.IsSameQ(otherEx, es)
}

func (this *Power) DeepCopy() Ex {
	return &Power{
		this.Base.DeepCopy(),
		this.Power.DeepCopy(),
	}
}
