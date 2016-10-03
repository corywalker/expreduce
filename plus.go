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
	origLen := len(a.Addends)
	offset := 0
	for i := 0; i < origLen; i++ {
		j := i + offset
		e := a.Addends[j]
		subadd, isadd := e.(*Plus)
		if isadd {
			start := j
			end := j + 1
			if j == 0 {
				a.Addends = append(subadd.Addends, a.Addends[end:]...)
			} else if j == len(a.Addends)-1 {
				a.Addends = append(a.Addends[:start], subadd.Addends...)
			} else {
				a.Addends = append(append(a.Addends[:start], subadd.Addends...), a.Addends[end:]...)
			}
			offset += len(subadd.Addends) - 1
		}
	}

	// If any of the addends are Sequence's, merge them with a and remove them
	origLen = len(a.Addends)
	offset = 0
	for i := 0; i < origLen; i++ {
		j := i + offset
		e := a.Addends[j]
		seq, isseq := e.(*Sequence)
		if isseq {
			start := j
			end := j + 1
			if j == 0 {
				a.Addends = append(seq.Arguments, a.Addends[end:]...)
			} else if j == len(a.Addends)-1 {
				a.Addends = append(a.Addends[:start], seq.Arguments...)
			} else {
				a.Addends = append(append(a.Addends[:start], seq.Arguments...), a.Addends[end:]...)
			}
			offset += len(seq.Arguments) - 1
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

	if len(a.Addends) == 1 {
		f, fOk := a.Addends[0].(*Flt)
		if fOk {
			if f.Val.Cmp(big.NewFloat(0)) == 0 {
				return f
			}
		}
		i, iOk := a.Addends[0].(*Integer)
		if iOk {
			if i.Val.Cmp(big.NewInt(0)) == 0 {
				return i
			}
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
	oldVars := es.GetDefinedSnapshot()
	es.log.Debugf(es.Pre() + "In Plus.Replace. First trying this.IsMatchQ(r.Lhs, es).")
	es.log.Debugf(es.Pre()+"Rule r is: %s", r.ToString())
	matchq := this.IsMatchQ(r.Lhs, es)
	toreturn := r.Rhs.DeepCopy().Eval(es)
	es.ClearPD()
	es.defined = oldVars
	if matchq {
		es.log.Debugf(es.Pre()+"After MatchQ, rule is: %s", r.ToString())
		es.log.Debugf(es.Pre()+"MatchQ succeeded. Returning r.Rhs: %s", r.Rhs.ToString())
		return toreturn
	}
	//es.log.Debugf(es.Pre()+"MatchQ failed. Dropping to IterableReplace")

	//IterableReplace(&this.Addends, r, es)
	rConv, ok := r.Lhs.(*Plus)
	if ok {
		es.log.Debugf(es.Pre() + "r.Lhs is a Plus. Now running CommutativeReplace")
		CommutativeReplace(&this.Addends, rConv.Addends, r.Rhs, es)
	}
	es.log.Debugf(es.Pre()+"Ex before iterative replace: %s", this.ToString())
	for i := range this.Addends {
		this.Addends[i] = this.Addends[i].Replace(r, es)
	}
	es.log.Debugf(es.Pre()+"Ex after iterative replace: %s", this.ToString())
	es.log.Debugf(es.Pre()+"Before eval. Context: %v\n", es.ToString())
	return this.Eval(es)
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
	if IsBlankTypeCapturing(otherEx, this, "Plus", es) {
		return true
	}
	thisEx := this.Eval(es)
	otherEx = otherEx.Eval(es)
	this, ok := thisEx.(*Plus)
	if !ok {
		return thisEx.IsMatchQ(otherEx, es)
	}
	other, ok := otherEx.(*Plus)
	if !ok {
		return false
	}
	return CommutativeIsMatchQ(this.Addends, other.Addends, es)
}

func (this *Plus) DeepCopy() Ex {
	var thiscopy = &Plus{}
	for i := range this.Addends {
		thiscopy.Addends = append(thiscopy.Addends, this.Addends[i].DeepCopy())
	}
	return thiscopy
}
