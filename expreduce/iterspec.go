package expreduce

import "math/big"

type IterSpec struct {
	i       Ex
	iName   string
	iMin    *Integer
	iMax    *Integer
	curr    int64
	iMaxInt int64
}

func IterSpecFromList(es *EvalState, listEx Ex) (is IterSpec, isOk bool) {
	listEx = evalIterSpecCandidate(es, listEx)
	list, isList := HeadAssertion(listEx, "List")
	if isList {
		iOk, iMinOk, iMaxOk := false, false, false
		if len(list.Parts) > 2 {
			iAsSymbol, iIsSymbol := list.Parts[1].(*Symbol)
			if iIsSymbol {
				iOk = true
				is.i = iAsSymbol
				is.iName = iAsSymbol.Name
			}
			iAsExpression, iIsExpression := list.Parts[1].(*Expression)
			if iIsExpression {
				headAsSymbol, headIsSymbol := iAsExpression.Parts[0].(*Symbol)
				if headIsSymbol {
					iOk = true
					is.i = iAsExpression
					is.iName = headAsSymbol.Name
				}
			}
		}
		if len(list.Parts) == 3 {
			is.iMin, iMinOk = &Integer{big.NewInt(1)}, true
			is.iMax, iMaxOk = list.Parts[2].(*Integer)
		} else if len(list.Parts) == 4 {
			is.iMin, iMinOk = list.Parts[2].(*Integer)
			is.iMax, iMaxOk = list.Parts[3].(*Integer)
		}
		if iOk && iMinOk && iMaxOk {
			is.Reset()
			return is, true
		}
	}
	return is, false
}

func (this *IterSpec) Reset() {
	this.curr = this.iMin.Val.Int64()
	this.iMaxInt = this.iMax.Val.Int64()
}

func (this *IterSpec) Next() {
	this.curr++
}

func (this *IterSpec) Cont() bool {
	return this.curr <= this.iMaxInt
}

type MultiIterSpec struct {
	iSpecs     []IterSpec
	origDefs   []Ex
	isOrigDefs []bool
	cont       bool
}

func MultiIterSpecFromLists(es *EvalState, lists []Ex) (mis MultiIterSpec, isOk bool) {
	// Retrieve variables of iteration
	mis.cont = true
	for i := range lists {
		is, isOk := IterSpecFromList(es, lists[i])
		if !isOk {
			return mis, false
		}
		mis.iSpecs = append(mis.iSpecs, is)
	}
	return mis, true
}

func (this *MultiIterSpec) Next() {
	for i := len(this.iSpecs) - 1; i >= 0; i-- {
		this.iSpecs[i].Next()
		if this.iSpecs[i].Cont() {
			return
		}
		this.iSpecs[i].Reset()
	}
	this.cont = false
}

func (this *MultiIterSpec) Cont() bool {
	return this.cont
}

func (this *MultiIterSpec) TakeVarSnapshot(es *EvalState) {
	this.origDefs = make([]Ex, len(this.iSpecs))
	this.isOrigDefs = make([]bool, len(this.iSpecs))
	for i := range this.iSpecs {
		this.origDefs[i], this.isOrigDefs[i] = es.GetDef(this.iSpecs[i].iName, this.iSpecs[i].i)
	}
}

func (this *MultiIterSpec) RestoreVarSnapshot(es *EvalState) {
	for i := range this.iSpecs {
		if this.isOrigDefs[i] {
			es.Define(this.iSpecs[i].iName, this.iSpecs[i].i, this.origDefs[i])
		} else {
			es.Clear(this.iSpecs[i].iName)
		}
	}
}

func (this *MultiIterSpec) DefineCurrent(es *EvalState) {
	for i := range this.iSpecs {
		es.Define(this.iSpecs[i].iName, this.iSpecs[i].i, &Integer{big.NewInt(this.iSpecs[i].curr)})
	}
}

func (this *Expression) EvalIterationFunc(es *EvalState, init Ex, op string) Ex {
	if len(this.Parts) >= 3 {
		mis, isOk := MultiIterSpecFromLists(es, this.Parts[2:])
		if isOk {
			// Simulate evaluation within Block[]
			mis.TakeVarSnapshot(es)
			var toReturn Ex = init
			for mis.Cont() {
				mis.DefineCurrent(es)
				toReturn = (&Expression{[]Ex{&Symbol{op}, toReturn, this.Parts[1].DeepCopy().Eval(es)}}).Eval(es)
				mis.Next()
			}
			mis.RestoreVarSnapshot(es)
			return toReturn
		}
	}
	return this
}

func evalIterSpecCandidate(es *EvalState, cand Ex) Ex {
	// Special handling for Lists, which might have variables of iteration in
	// them.
	list, isList := HeadAssertion(cand, "List")
	if isList {
		toReturn := &Expression{[]Ex{&Symbol{"List"}}}
		for i := 1; i < len(list.Parts); i++ {
			toAdd := list.Parts[i].DeepCopy()
			// Do not evaluate the variable of iteration. Even if "n" is
			// defined already, we just want it to be "n".
			if i != 1 {
				toAdd = toAdd.Eval(es)
			}
			toReturn.Parts = append(toReturn.Parts, toAdd)
		}
		return toReturn
	}
	// We should attempt to evaluate all non-Lists, since we expect them to not
	// have any variables of iteration in them.
	return cand.Eval(es)
}
