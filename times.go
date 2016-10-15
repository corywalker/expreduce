package cas

import "bytes"
import "math/big"

func (this *Expression) EvalTimes(es *EvalState) Ex {
	// Calls without argument receive identity values
	if len(this.Parts) == 1 {
		return &Integer{big.NewInt(1)}
	}

	multiplicands := this.Parts[1:len(this.Parts)]
	// Start by evaluating each multiplicand
	for i := range multiplicands {
		multiplicands[i] = multiplicands[i].Eval(es)
	}

	// If any of the multiplicands are also Times, merge them with m and remove them
	origLen := len(multiplicands)
	offset := 0
	for i := 0; i < origLen; i++ {
		j := i + offset
		e := multiplicands[j]
		submul, ismul := HeadAssertion(e, "Times")
		if ismul {
			subMultiplicands := submul.Parts[1:len(submul.Parts)]
			start := j
			end := j + 1
			if j == 0 {
				multiplicands = append(subMultiplicands, multiplicands[end:]...)
			} else if j == len(multiplicands)-1 {
				multiplicands = append(multiplicands[:start], subMultiplicands...)
			} else {
				multiplicands = append(append(multiplicands[:start], subMultiplicands...), multiplicands[end:]...)
			}
			offset += len(subMultiplicands) - 1
		}
	}

	// If this expression contains any floats, convert everything possible to
	// a float
	if ExArrayContainsFloat(multiplicands) {
		for i, e := range multiplicands {
			subint, isint := e.(*Integer)
			if isint {
				newfloat := big.NewFloat(0)
				newfloat.SetInt(subint.Val)
				multiplicands[i] = &Flt{newfloat}
			}
		}
	}

	// If there is a zero in the expression, return zero
	for _, e := range multiplicands {
		f, ok := e.(*Flt)
		if ok {
			if f.Val.Cmp(big.NewFloat(0)) == 0 {
				return &Flt{big.NewFloat(0)}
			}
		}
	}

	// Geometrically accumulate floating point values towards the end of the expression
	//es.Debugf("Before accumulating floats: %s", m)
	origLen = len(multiplicands)
	offset = 0
	var lastf *Flt = nil
	var lastfj int = 0
	for i := 0; i < origLen; i++ {
		j := i - offset
		e := multiplicands[j]
		f, ok := e.(*Flt)
		if ok {
			if lastf != nil {
				es.Debugf("Encountered float. i=%d, j=%d, lastf=%s, lastfj=%d", i, j, lastf, lastfj)
				f.Val.Mul(f.Val, lastf.Val)
				//lastf.Val = big.NewFloat(1)
				multiplicands = append(multiplicands[:lastfj], multiplicands[lastfj+1:]...)
				offset++
				es.Debugf("After deleting: %s", this)
			}
			lastf = f
			lastfj = i - offset
		}
	}
	//es.Debugf(es.Pre() +"After accumulating floats: %s", m)

	if len(multiplicands) == 1 {
		f, fOk := multiplicands[0].(*Flt)
		if fOk {
			if f.Val.Cmp(big.NewFloat(0)) == 1 {
				return f
			}
		}
		i, iOk := multiplicands[0].(*Integer)
		if iOk {
			if i.Val.Cmp(big.NewInt(0)) == 1 {
				return i
			}
		}
	}

	// Remove one Floats
	/*
		for i := len(multiplicands) - 1; i >= 0; i-- {
			f, ok := multiplicands[i].(*Flt)
			if ok && f.Val.Cmp(big.NewFloat(1)) == 0 {
				multiplicands[i] = multiplicands[len(multiplicands)-1]
				multiplicands[len(multiplicands)-1] = nil
				multiplicands = multiplicands[:len(multiplicands)-1]
			}
		}
	*/

	// Geometrically accumulate integer values towards the end of the expression
	var lasti *Integer = nil
	for _, e := range multiplicands {
		theint, ok := e.(*Integer)
		if ok {
			if lasti != nil {
				theint.Val.Mul(theint.Val, lasti.Val)
				lasti.Val = big.NewInt(1)
			}
			lasti = theint
		}
	}

	// Remove one Integers
	for i := len(multiplicands) - 1; i >= 0; i-- {
		theint, ok := multiplicands[i].(*Integer)
		if ok && theint.Val.Cmp(big.NewInt(1)) == 0 && len(multiplicands) > 1 {
			multiplicands[i] = multiplicands[len(multiplicands)-1]
			multiplicands[len(multiplicands)-1] = nil
			multiplicands = multiplicands[:len(multiplicands)-1]
		}
	}

	// If one expression remains, replace this Times with the expression
	if len(multiplicands) == 1 {
		return multiplicands[0]
	}

	// Automatically Expand negations (*-1), not (*-1.) of a Plus expression
	if len(multiplicands) == 2 {
		leftint, leftintok := multiplicands[0].(*Integer)
		rightint, rightintok := multiplicands[1].(*Integer)
		leftplus, leftplusok := HeadAssertion(multiplicands[0], "Plus")
		rightplus, rightplusok := HeadAssertion(multiplicands[1], "Plus")
		var theInt *Integer = nil
		var thePlus *Expression = nil
		if leftintok {
			theInt = leftint
		}
		if rightintok {
			theInt = rightint
		}
		if leftplusok {
			thePlus = leftplus
		}
		if rightplusok {
			thePlus = rightplus
		}
		if theInt != nil && thePlus != nil {
			if theInt.Val.Cmp(big.NewInt(-1)) == 0 {
				toreturn := &Expression{[]Ex{&Symbol{"Plus"}}}
				addends := thePlus.Parts[1:len(thePlus.Parts)]
				for i := range addends {
					toAppend := &Expression{[]Ex{
						&Symbol{"Times"},
						addends[i],
						&Integer{big.NewInt(-1)},
					}}
					toreturn.Parts = append(toreturn.Parts, toAppend)
				}
				return toreturn.Eval(es)
			}
		}
	}

	this.Parts = this.Parts[0:1]
	this.Parts = append(this.Parts, multiplicands...)
	return this
}

func (this *Expression) ToStringTimes() string {
	multiplicands := this.Parts[1:len(this.Parts)]
	var buffer bytes.Buffer
	buffer.WriteString("(")
	for i, e := range multiplicands {
		buffer.WriteString(e.String())
		if i != len(multiplicands)-1 {
			buffer.WriteString(" * ")
		}
	}
	buffer.WriteString(")")
	return buffer.String()
}
