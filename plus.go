package cas

import "bytes"
import "math/big"

// A sequence of Expressions to be added together
type Plus struct {
	Addends []Ex
}

func (this *Plus) ContainsFloat() bool {
	res := false
	for _, e := range this.Addends {
		_, isfloat := e.(*Flt)
		res = res || isfloat
	}
	return res
}

func (a *Plus) Eval(es *EvalState) Ex {
	// Start by evaluating each addend
	for i := range a.Addends {
		a.Addends[i] = a.Addends[i].Eval(es)
	}

	// If any of the addends are also Plus's, merge them with a and remove them
	// We can easily remove an item by replacing it with a zero int.
	for i, e := range a.Addends {
		subadd, isadd := e.(*Plus)
		if isadd {
			a.Addends = append(a.Addends, subadd.Addends...)
			a.Addends[i] = &Integer{big.NewInt(0)}
		}
	}

	// If this expression contains any floats, convert everything possible to
	// a float
	if a.ContainsFloat() {
		for i, e := range a.Addends {
			subint, isint := e.(*Integer)
			if isint {
				newfloat := big.NewFloat(0)
				newfloat.SetInt(subint.Val)
				a.Addends[i] = &Flt{newfloat}
			}
		}
	}

	// Accumulate floating point values towards the end of the expression
	var lastf *Flt = nil
	for _, e := range a.Addends {
		f, ok := e.(*Flt)
		if ok {
			if lastf != nil {
				f.Val.Add(f.Val, lastf.Val)
				lastf.Val = big.NewFloat(0)
			}
			lastf = f
		}
	}

	// Remove zero Floats
	for i := len(a.Addends) - 1; i >= 0; i-- {
		f, ok := a.Addends[i].(*Flt)
		if ok && f.Val.Cmp(big.NewFloat(0)) == 0 {
			a.Addends[i] = a.Addends[len(a.Addends)-1]
			a.Addends[len(a.Addends)-1] = nil
			a.Addends = a.Addends[:len(a.Addends)-1]
		}
	}

	// Accumulate integer values towards the end of the expression
	var lasti *Integer = nil
	for _, e := range a.Addends {
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
	for i := len(a.Addends) - 1; i >= 0; i-- {
		theint, ok := a.Addends[i].(*Integer)
		if ok && theint.Val.Cmp(big.NewInt(0)) == 0 {
			a.Addends[i] = a.Addends[len(a.Addends)-1]
			a.Addends[len(a.Addends)-1] = nil
			a.Addends = a.Addends[:len(a.Addends)-1]
		}
	}

	// If one expression remains, replace this Plus with the expression
	if len(a.Addends) == 1 {
		return a.Addends[0]
	}

	return a
}

func (this *Plus) Replace(r *Rule, es *EvalState) Ex {
	if this.IsMatchQ(r.Lhs, es) {
		return r.Rhs
	}
	IterableReplace(&this.Addends, r, es)
	rConv, ok := r.Lhs.(*Plus)
	if ok {
		CommutativeReplace(&this.Addends, rConv.Addends, r.Rhs, es)
	}
	for i := range this.Addends {
		this.Addends[i] = this.Addends[i].Replace(r, es)
	}
	return this
}

func (a *Plus) ToString() string {
	var buffer bytes.Buffer
	buffer.WriteString("(")
	for i, e := range a.Addends {
		buffer.WriteString(e.ToString())
		if i != len(a.Addends)-1 {
			buffer.WriteString(" + ")
		}
	}
	buffer.WriteString(")")
	return buffer.String()
}

func (this *Plus) IsEqual(otherEx Ex, es *EvalState) string {
	thisEx := this.Eval(es)
	otherEx = otherEx.Eval(es)
	this, ok := thisEx.(*Plus)
	if !ok {
		return thisEx.IsEqual(otherEx, es)
	}
	other, ok := otherEx.(*Plus)
	if !ok {
		return "EQUAL_FALSE"
	}
	return CommutativeIsEqual(this.Addends, other.Addends, es)
}

func (this *Plus) IsSameQ(otherEx Ex, es *EvalState) bool {
	return this.IsEqual(otherEx, es) == "EQUAL_TRUE"
}

func (this *Plus) IsMatchQ(otherEx Ex, es *EvalState) bool {
	return this.IsSameQ(otherEx, es)
}

func (this *Plus) DeepCopy() Ex {
	var thiscopy = &Plus{}
	for i := range this.Addends {
		thiscopy.Addends = append(thiscopy.Addends, this.Addends[i].DeepCopy())
	}
	return thiscopy
}
