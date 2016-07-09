package cas

import "bytes"
import "math/big"

// A sequence of Expressions to be multiplied together
type Times struct {
	Multiplicands []Ex
}

func (this *Times) ContainsFloat() bool {
	res := false
	for _, e := range this.Multiplicands {
		_, isfloat := e.(*Flt)
		res = res || isfloat
	}
	return res
}

func (m *Times) Eval(es *EvalState) Ex {
	// Start by evaluating each multiplicand
	for i := range m.Multiplicands {
		m.Multiplicands[i] = m.Multiplicands[i].Eval(es)
	}

	// If any of the multiplicands are also Times, merge them with m and remove them
	// We can easily remove an item by replacing it with a one int.
	origLen := len(m.Multiplicands)
	offset := 0
	for i := 0; i < origLen; i++ {
		j := i + offset
		e := m.Multiplicands[j]
		submul, isadd := e.(*Times)
		if isadd {
			start := j
			end := j+1
			if j == 0 {
				m.Multiplicands = append(submul.Multiplicands, m.Multiplicands[end:]...)
			} else if j == len(m.Multiplicands) - 1 {
				m.Multiplicands = append(m.Multiplicands[:start], submul.Multiplicands...)
			} else {
				m.Multiplicands = append(append(m.Multiplicands[:start], submul.Multiplicands...), m.Multiplicands[end:]...)
			}
			//m.Multiplicands[i] = &Integer{big.NewInt(0)}
			offset += len(submul.Multiplicands) - 1
		}
	}

	// If this expression contains any floats, convert everything possible to
	// a float
	if m.ContainsFloat() {
		for i, e := range m.Multiplicands {
			subint, isint := e.(*Integer)
			if isint {
				newfloat := big.NewFloat(0)
				newfloat.SetInt(subint.Val)
				m.Multiplicands[i] = &Flt{newfloat}
			}
		}
	}

	// If there is a zero in the expression, return zero
	for _, e := range m.Multiplicands {
		f, ok := e.(*Flt)
		if ok {
			if f.Val.Cmp(big.NewFloat(0)) == 0 {
				return &Flt{big.NewFloat(0)}
			}
		}
	}

	// Geometrically accumulate floating point values towards the end of the expression
	var lastf *Flt = nil
	for _, e := range m.Multiplicands {
		f, ok := e.(*Flt)
		if ok {
			if lastf != nil {
				f.Val.Mul(f.Val, lastf.Val)
				lastf.Val = big.NewFloat(1)
			}
			lastf = f
		}
	}

	// Remove one Floats
	for i := len(m.Multiplicands) - 1; i >= 0; i-- {
		f, ok := m.Multiplicands[i].(*Flt)
		if ok && f.Val.Cmp(big.NewFloat(1)) == 0 {
			m.Multiplicands[i] = m.Multiplicands[len(m.Multiplicands)-1]
			m.Multiplicands[len(m.Multiplicands)-1] = nil
			m.Multiplicands = m.Multiplicands[:len(m.Multiplicands)-1]
		}
	}

	// Geometrically accumulate integer values towards the end of the expression
	var lasti *Integer = nil
	for _, e := range m.Multiplicands {
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
	for i := len(m.Multiplicands) - 1; i >= 0; i-- {
		theint, ok := m.Multiplicands[i].(*Integer)
		if ok && theint.Val.Cmp(big.NewInt(1)) == 0 {
			m.Multiplicands[i] = m.Multiplicands[len(m.Multiplicands)-1]
			m.Multiplicands[len(m.Multiplicands)-1] = nil
			m.Multiplicands = m.Multiplicands[:len(m.Multiplicands)-1]
		}
	}

	// If one expression remains, replace this Times with the expression
	if len(m.Multiplicands) == 1 {
		return m.Multiplicands[0]
	}

	return m
}

func (this *Times) Replace(r *Rule, es *EvalState) Ex {
	es.logDepth++
	oldVars := es.GetDefinedSnapshot()
	es.log.Debugf(es.Pre() + "In Times.Replace. First trying this.IsMatchQ(r.Lhs, es).")
	es.log.Debugf(es.Pre()+"Rule r is: %s", r.ToString())
	matchq := this.IsMatchQ(r.Lhs, es)
	toreturn := r.Rhs.DeepCopy().Eval(es)
	es.ClearPD()
	es.defined = oldVars
	if matchq {
		es.log.Debugf(es.Pre()+"After MatchQ, rule is: %s", r.ToString())
		es.log.Debugf(es.Pre()+"MatchQ succeeded. Returning r.Rhs: %s", r.Rhs.ToString())
		es.logDepth--
		return toreturn
	}

	//IterableReplace(&this.Multiplicands, r, es)
	rConv, ok := r.Lhs.(*Times)
	if ok {
		es.log.Debugf(es.Pre() + "r.Lhs is a Times. Now running CommutativeReplace")
		CommutativeReplace(&this.Multiplicands, rConv.Multiplicands, r.Rhs, es)
	}
	es.log.Debugf(es.Pre()+"Ex before iterative replace: %s", this.ToString())
	for i := range this.Multiplicands {
		this.Multiplicands[i] = this.Multiplicands[i].Replace(r, es)
	}
	es.log.Debugf(es.Pre()+"Ex after iterative replace: %s", this.ToString())
	es.log.Debugf(es.Pre()+"Before eval. Context: %v\n", es.ToString())
	es.logDepth--
	return this.Eval(es)
}

func (m *Times) ToString() string {
	var buffer bytes.Buffer
	buffer.WriteString("(")
	for i, e := range m.Multiplicands {
		buffer.WriteString(e.ToString())
		if i != len(m.Multiplicands)-1 {
			buffer.WriteString(" * ")
		}
	}
	buffer.WriteString(")")
	return buffer.String()
}

func (this *Times) IsEqual(otherEx Ex, es *EvalState) string {
	thisEx := this.Eval(es)
	otherEx = otherEx.Eval(es)
	this, ok := thisEx.(*Times)
	if !ok {
		return thisEx.IsEqual(otherEx, es)
	}
	other, ok := otherEx.(*Times)
	if !ok {
		return "EQUAL_UNK"
	}
	return CommutativeIsEqual(this.Multiplicands, other.Multiplicands, es)
}

func (this *Times) IsSameQ(otherEx Ex, es *EvalState) bool {
	return this.IsEqual(otherEx, es) == "EQUAL_TRUE"
}

func (this *Times) IsMatchQ(otherEx Ex, es *EvalState) bool {
	if IsBlankType(otherEx, "Times") {
		return true
	}
	thisEx := this.Eval(es)
	otherEx = otherEx.Eval(es)
	this, ok := thisEx.(*Times)
	if !ok {
		return thisEx.IsMatchQ(otherEx, es)
	}
	other, ok := otherEx.(*Times)
	if !ok {
		return false
	}
	return CommutativeIsMatchQ(this.Multiplicands, other.Multiplicands, es)
}

func (this *Times) DeepCopy() Ex {
	var thiscopy = &Times{}
	for i := range this.Multiplicands {
		thiscopy.Multiplicands = append(thiscopy.Multiplicands, this.Multiplicands[i].DeepCopy())
	}
	return thiscopy
}
