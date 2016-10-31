package cas

import "bytes"
import "math/big"

func (this *Expression) ToStringList() string {
	var buffer bytes.Buffer
	buffer.WriteString("{")
	for i, e := range this.Parts[1:] {
		buffer.WriteString(e.String())
		if i != len(this.Parts[1:])-1 {
			buffer.WriteString(", ")
		}
	}
	buffer.WriteString("}")
	return buffer.String()
}

func (this *Expression) EvalLength(es *EvalState) Ex {
	if len(this.Parts) != 2 {
		return this
	}

	list, isList := HeadAssertion(this.Parts[1], "List")
	if isList {
		return &Integer{big.NewInt(int64(len(list.Parts) - 1))}
	}
	return this
}

func (this *Expression) EvalTable(es *EvalState) Ex {
	if len(this.Parts) != 3 {
		return this
	}

	list, isList := HeadAssertion(this.Parts[2], "List")
	if isList {
		if len(list.Parts) == 4 {
			i, iOk := list.Parts[1].(*Symbol)
			iMin, iMinOk := list.Parts[2].(*Integer)
			iMax, iMaxOk := list.Parts[3].(*Integer)
			if iOk && iMinOk && iMaxOk {
				origDef, isOrigDef := es.GetDef(i.Name, i)
				toReturn := &Expression{[]Ex{&Symbol{"List"}}}
				iMaxInt := iMax.Val.Int64()
				for curr := iMin.Val.Int64(); curr <= iMaxInt; curr++ {
					es.Define(i.Name, i, &Integer{big.NewInt(curr)})
					toReturn.Parts = append(toReturn.Parts, this.Parts[1].DeepCopy().Eval(es))
				}
				if isOrigDef {
					es.Define(i.Name, i, origDef)
				} else {
					es.Clear(i.Name)
				}
				return toReturn
			}
		}
	}
	return this
}

func (this *Expression) EvalIterationFunc(es *EvalState, init Ex, op string) Ex {
	if len(this.Parts) != 3 {
		return this
	}

	list, isList := HeadAssertion(this.Parts[2], "List")
	if isList {
		// Retrieve variables of iteration
		var i *Symbol
		var iMin, iMax *Integer
		iOk, iMinOk, iMaxOk := false, false, false
		if len(list.Parts) == 3 {
			i, iOk = list.Parts[1].(*Symbol)
			iMin, iMinOk = &Integer{big.NewInt(1)}, true
			iMax, iMaxOk = list.Parts[2].(*Integer)
		} else if len(list.Parts) == 4 {
			i, iOk = list.Parts[1].(*Symbol)
			iMin, iMinOk = list.Parts[2].(*Integer)
			iMax, iMaxOk = list.Parts[3].(*Integer)
		}

		if iOk && iMinOk && iMaxOk {
			origDef, isOrigDef := es.GetDef(i.Name, i)
			var toReturn Ex = init
			iMaxInt := iMax.Val.Int64()
			for curr := iMin.Val.Int64(); curr <= iMaxInt; curr++ {
				es.Define(i.Name, i, &Integer{big.NewInt(curr)})
				toReturn = (&Expression{[]Ex{&Symbol{op}, toReturn, this.Parts[1].DeepCopy().Eval(es)}}).Eval(es)
			}
			if isOrigDef {
				es.Define(i.Name, i, origDef)
			} else {
				es.Clear(i.Name)
			}
			return toReturn
		}
	}
	return this
}

func (this *Expression) EvalSum(es *EvalState) Ex {
	return this.EvalIterationFunc(es, &Integer{big.NewInt(0)}, "Plus")
}

func (this *Expression) EvalProduct(es *EvalState) Ex {
	return this.EvalIterationFunc(es, &Integer{big.NewInt(1)}, "Times")
}

func (this *Expression) EvalMemberQ(es *EvalState) Ex {
	if len(this.Parts) != 3 {
		return this
	}
	list, isList := HeadAssertion(this.Parts[1], "List")
	if isList {
		for _, exp := range list.Parts {
			if res, _ := IsMatchQ(exp, this.Parts[2], &es.PDManager, &es.CASLogger); res {
				return &Symbol{"True"}
			}
		}
	}
	return &Symbol{"False"}
}

func (this *Expression) EvalMap(es *EvalState) Ex {
	if len(this.Parts) != 3 {
		return this
	}

	list, isList := HeadAssertion(this.Parts[2], "List")
	if isList {
		toReturn := &Expression{[]Ex{&Symbol{"List"}}}
		for i := 1; i < len(list.Parts); i++ {
			toReturn.Parts = append(toReturn.Parts, &Expression{[]Ex{
				this.Parts[1].DeepCopy(),
				list.Parts[i].DeepCopy(),
			}})
		}
		return toReturn
	}
	return this.Parts[2]
}

func (this *Expression) EvalArray(es *EvalState) Ex {
	if len(this.Parts) != 3 {
		return this
	}

	nInt, nOk := this.Parts[2].(*Integer)
	if nOk {
		n := nInt.Val.Int64()
		toReturn := &Expression{[]Ex{&Symbol{"List"}}}
		for i := int64(1); i <= n; i++ {
			toReturn.Parts = append(toReturn.Parts, &Expression{[]Ex{
				this.Parts[1].DeepCopy(),
				&Integer{big.NewInt(i)},
			}})
		}
		return toReturn
	}
	return this.Parts[2]
}
