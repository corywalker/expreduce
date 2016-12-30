package cas

import "bytes"
import "math/big"

func (this *Expression) EvalPlus(es *EvalState) Ex {
	// Calls without argument receive identity values
	if len(this.Parts) == 1 {
		return &Integer{big.NewInt(0)}
	}

	addends := this.Parts[1:len(this.Parts)]
	// If this expression contains any floats, convert everything possible to
	// a float
	if ExArrayContainsFloat(addends) {
		for i, e := range addends {
			subint, isint := e.(*Integer)
			subrat, israt := e.(*Rational)
			if isint {
				newfloat := big.NewFloat(0)
				newfloat.SetInt(subint.Val)
				addends[i] = &Flt{newfloat}
			} else if israt {
				num := big.NewFloat(0)
				den := big.NewFloat(0)
				newquo := big.NewFloat(0)
				num.SetInt(subrat.Num)
				den.SetInt(subrat.Den)
				newquo.Quo(num, den)
				addends[i] = &Flt{newquo}
			}
		}
	}

	// Accumulate floating point values towards the end of the expression
	var lastf *Flt = nil
	for _, e := range addends {
		f, ok := e.(*Flt)
		if ok {
			if lastf != nil {
				f.Val.Add(f.Val, lastf.Val)
				lastf.Val = big.NewFloat(0)
			}
			lastf = f
		}
	}

	if len(addends) == 1 {
		f, fOk := addends[0].(*Flt)
		if fOk {
			if f.Val.Cmp(big.NewFloat(0)) == 0 {
				return f
			}
		}
		i, iOk := addends[0].(*Integer)
		if iOk {
			if i.Val.Cmp(big.NewInt(0)) == 0 {
				return i
			}
		}
	}

	// Remove zero Floats
	for i := len(addends) - 1; i >= 0; i-- {
		f, ok := addends[i].(*Flt)
		if ok && f.Val.Cmp(big.NewFloat(0)) == 0 && len(addends) > 1 {
			addends[i] = addends[len(addends)-1]
			addends[len(addends)-1] = nil
			addends = addends[:len(addends)-1]
		}
	}

	// Accumulate integer values towards the end of the expression
	var lasti *Integer = nil
	for _, e := range addends {
		i, ok := e.(*Integer)
		if ok {
			if lasti != nil {
				i.Val.Add(i.Val, lasti.Val)
				lasti.Val = big.NewInt(0)
			}
			lasti = i
		}
	}

	// Accumulate rational values towards the end of the expression
	var lastr *Rational = nil
	for _, e := range addends {
		therat, ok := e.(*Rational)
		if ok {
			if lastr != nil {
				tmp := big.NewInt(0)
				// lastrNum/lastrDen + theratNum/theratDen // Together
				tmp.Mul(therat.Den, lastr.Num)
				therat.Den.Mul(therat.Den, lastr.Den)
				therat.Num.Mul(therat.Num, lastr.Den)
				therat.Num.Add(therat.Num, tmp)
				lastr.Num = big.NewInt(0)
				lastr.Den = big.NewInt(1)
			}
			lastr = therat
		}
	}

	// If there is one Integer and one Rational left, merge the Integer into
	// the Rational
	if lasti != nil && lastr != nil {
		lasti.Val.Mul(lasti.Val, lastr.Den)
		lastr.Num.Add(lastr.Num, lasti.Val)
		lasti.Val = big.NewInt(0)
	}

	// Remove zero Integers and Rationals
	for i := len(addends) - 1; i >= 0; i-- {
		toRemove := false
		theint, isInt := addends[i].(*Integer)
		if isInt {
			toRemove = theint.Val.Cmp(big.NewInt(0)) == 0
		}
		therat, isRat := addends[i].(*Rational)
		if isRat {
			toRemove = therat.Num.Cmp(big.NewInt(0)) == 0 && therat.Den.Cmp(big.NewInt(1)) == 0
		}
		if toRemove && len(addends) > 1 {
			addends[i] = addends[len(addends)-1]
			addends[len(addends)-1] = nil
			addends = addends[:len(addends)-1]
		}
	}

	// If one expression remains, replace this Plus with the expression
	if len(addends) == 1 {
		return addends[0]
	}

	this.Parts = this.Parts[0:1]
	this.Parts = append(this.Parts, addends...)
	return this
}

func (this *Expression) ToStringPlus() string {
	addends := this.Parts[1:len(this.Parts)]
	var buffer bytes.Buffer
	buffer.WriteString("(")
	for i, e := range addends {
		buffer.WriteString(e.String())
		if i != len(addends)-1 {
			buffer.WriteString(" + ")
		}
	}
	buffer.WriteString(")")
	return buffer.String()
}

func GetPlusDefinitions() (defs []Definition) {
	return
}
