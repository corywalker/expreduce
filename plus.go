package cas

import "bytes"
import "math/big"

func (this *Expression) EvalPlus(es *EvalState) Ex {
	// Calls without argument receive identity values
	if len(this.Parts) == 1 {
		return &Integer{big.NewInt(0)}
	}

	addends := this.Parts[1:len(this.Parts)]
	// Start by evaluating each addend
	for i := range addends {
		addends[i] = addends[i].Eval(es)
	}

	// If any of the addends are also Plus's, merge them with a and remove them
	origLen := len(addends)
	offset := 0
	for i := 0; i < origLen; i++ {
		j := i + offset
		e := addends[j]
		subadd, isadd := HeadAssertion(e, "Plus")
		if isadd {
			subAddends := subadd.Parts[1:len(subadd.Parts)]
			start := j
			end := j + 1
			if j == 0 {
				addends = append(subAddends, addends[end:]...)
			} else if j == len(addends)-1 {
				addends = append(addends[:start], subAddends...)
			} else {
				addends = append(append(addends[:start], subAddends...), addends[end:]...)
			}
			offset += len(subAddends) - 1
		}
	}

	// If this expression contains any floats, convert everything possible to
	// a float
	if ExArrayContainsFloat(addends) {
		for i, e := range addends {
			subint, isint := e.(*Integer)
			if isint {
				newfloat := big.NewFloat(0)
				newfloat.SetInt(subint.Val)
				addends[i] = &Flt{newfloat}
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

	// Remove zero Integers
	for i := len(addends) - 1; i >= 0; i-- {
		theint, ok := addends[i].(*Integer)
		if ok && theint.Val.Cmp(big.NewInt(0)) == 0 && len(addends) > 1 {
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
