package expreduce

import "bytes"
import "math/big"
import "sort"

func (this *Expression) ToStringList(form string, context *String, contextPath *Expression) (bool, string) {
	if form == "FullForm" {
		return false, ""
	}
	var buffer bytes.Buffer
	buffer.WriteString("{")
	for i, e := range this.Parts[1:] {
		buffer.WriteString(e.StringForm(form, context, contextPath))
		if i != len(this.Parts[1:])-1 {
			buffer.WriteString(", ")
		}
	}
	buffer.WriteString("}")
	return true, buffer.String()
}

func MemberQ(components []Ex, item Ex, es *EvalState) bool {
	for _, part := range components {
		if matchq, _ := IsMatchQ(part, item, EmptyPD(), es); matchq {
			return true
		}
	}
	return false
}

func ValidatePadParams(this *Expression) (list *Expression, n int64, x Ex, valid bool) {
	valid = false
	x = &Integer{big.NewInt(0)}
	if len(this.Parts) == 4 {
		x = this.Parts[3]
	} else if len(this.Parts) != 3 {
		return
	}

	nInt, nIsInt := this.Parts[2].(*Integer)
	if !nIsInt {
		return
	}
	n = nInt.Val.Int64()

	list, listIsExpr := this.Parts[1].(*Expression)
	if !listIsExpr {
		return
	}

	valid = true
	return
}

func applyIndex(ex Ex, index Ex) (Ex, bool) {
	expr, isExpr := ex.(*Expression)
	if !isExpr {
		return nil, false
	}
	iInt, iIsInt := index.(*Integer)
	if iIsInt {
		if iInt.Val.Int64() >= int64(len(expr.Parts)) {
			return nil, false
		}
		return expr.Parts[iInt.Val.Int64()], true
	}
	iSym, iIsSym := index.(*Symbol)
	if iIsSym {
		if iSym.Name == "System`All" {
			return expr, true
		}
	}
	return nil, false
}

func ThreadExpr(expr *Expression) (*Expression, bool) {
	lengths := []int{}
	for i := 1; i < len(expr.Parts); i++ {
		list, isList := HeadAssertion(expr.Parts[i], "System`List")
		if isList {
			lengths = append(lengths, len(list.Parts)-1)
		}
	}
	if len(lengths) == 0 {
		return expr, false
	}
	allSame := true
	for i := range lengths {
		allSame = allSame && (lengths[0] == lengths[i])
	}
	if !allSame {
		return expr, false
	}
	listLen := lengths[0]
	toReturn := NewExpression([]Ex{&Symbol{"System`List"}})
	for listI := 0; listI < listLen; listI++ {
		thisExpr := NewExpression([]Ex{expr.Parts[0].DeepCopy()})
		for i := 1; i < len(expr.Parts); i++ {
			list, isList := HeadAssertion(expr.Parts[i], "System`List")
			if isList {
				thisExpr.Parts = append(thisExpr.Parts, list.Parts[listI+1])
			} else {
				thisExpr.Parts = append(thisExpr.Parts, expr.Parts[i])
			}
		}
		toReturn.Parts = append(toReturn.Parts, thisExpr)
	}
	return toReturn, true
}

func GetListDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name:     "List",
		toString: (*Expression).ToStringList,
	})
	defs = append(defs, Definition{
		Name: "Total",
	})
	defs = append(defs, Definition{
		Name: "Mean",
	})
	defs = append(defs, Definition{
		Name: "Table",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) >= 3 {
				mis, isOk := multiIterSpecFromLists(es, this.Parts[2:])
				if isOk {
					// Simulate evaluation within Block[]
					mis.takeVarSnapshot(es)
					toReturn := NewExpression([]Ex{&Symbol{"System`List"}})
					for mis.cont() {
						mis.defineCurrent(es)
						// TODO: use ReplacePD for this. We're only replacing
						// symbols. Don't need a full Eval.
						toReturn.Parts = append(toReturn.Parts, this.Parts[1].DeepCopy().Eval(es))
						es.Debugf("%v\n", toReturn)
						mis.next()
					}
					mis.restoreVarSnapshot(es)
					return toReturn
				}
			}
			return this
		},
	})
	defs = append(defs, Definition{
		Name: "MemberQ",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}
			expr, isExpr := this.Parts[1].(*Expression)
			if isExpr {
				if MemberQ(expr.Parts[1:], this.Parts[2], es) {
					return &Symbol{"System`True"}
				}
			}
			return &Symbol{"System`False"}
		},
	})
	defs = append(defs, Definition{
		Name: "Cases",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}

			expr, isExpr := this.Parts[1].(*Expression)
			if isExpr {
				toReturn := NewExpression([]Ex{&Symbol{"System`List"}})
				pattern := this.Parts[2]
				rule, isRule := HeadAssertion(this.Parts[2], "System`Rule")
				if isRule {
					if len(rule.Parts) != 3 {
						return toReturn
					}
					pattern = rule.Parts[1]
				}

				for i := 1; i < len(expr.Parts); i++ {
					if matchq, pd := IsMatchQ(expr.Parts[i], pattern, EmptyPD(), es); matchq {
						toAdd := expr.Parts[i]
						if isRule {
							toAdd = ReplacePD(rule.Parts[2], es, pd)
						}
						toReturn.Parts = append(toReturn.Parts, toAdd)
					}
				}

				return toReturn
			}
			return this
		},
	})
	defs = append(defs, Definition{
		Name: "DeleteCases",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}

			expr, isExpr := this.Parts[1].(*Expression)
			if isExpr {
				toReturn := NewExpression([]Ex{expr.Parts[0]})
				pattern := this.Parts[2]
				for i := 1; i < len(expr.Parts); i++ {
					if matchq, _ := IsMatchQ(expr.Parts[i], pattern, EmptyPD(), es); !matchq {
						toAdd := expr.Parts[i]
						toReturn.Parts = append(toReturn.Parts, toAdd)
					}
				}

				return toReturn
			}
			return this
		},
	})
	defs = append(defs, Definition{
		Name: "Union",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) == 1 {
				return NewExpression([]Ex{&Symbol{"System`List"}})
			}
			var firstHead Ex = nil
			var allParts *Expression = nil
			for _, part := range this.Parts[1:] {
				expr, isExpr := part.(*Expression)
				if !isExpr {
					return this
				}
				if firstHead == nil {
					firstHead = expr.Parts[0]
					allParts = NewExpression([]Ex{firstHead})
				} else if !IsSameQ(firstHead, expr.Parts[0], &es.CASLogger) {
					return this
				}
				allParts.Parts = append(allParts.Parts, expr.Parts[1:]...)
			}
			sort.Sort(allParts)
			toReturn := NewExpression([]Ex{firstHead})
			var lastEx Ex = nil
			for _, part := range allParts.Parts[1:] {
				if lastEx == nil || !IsSameQ(lastEx, part, &es.CASLogger) {
					lastEx = part
					toReturn.Parts = append(toReturn.Parts, part)
				}
			}

			return toReturn
		},
	})
	defs = append(defs, Definition{
		Name: "Complement",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) == 1 {
				return this
			}
			var firstHead Ex = nil
			exclusions := map[uint64]bool{}
			for _, part := range this.Parts[1:] {
				expr, isExpr := part.(*Expression)
				if !isExpr {
					return this
				}
				if firstHead == nil {
					firstHead = expr.Parts[0]
					continue
				} else if !IsSameQ(firstHead, expr.Parts[0], &es.CASLogger) {
					return this
				}
				for _, excludedPart := range expr.Parts[1:] {
					exclusions[hashEx(excludedPart)] = true
				}
			}
			toReturn := NewExpression([]Ex{firstHead})
			added := map[uint64]bool{}
			for _, part := range this.Parts[1].(*Expression).Parts[1:] {
				hash := hashEx(part)
				_, alreadyAdded := added[hash]
				_, excluded := exclusions[hash]
				if !excluded && !alreadyAdded {
					added[hash] = true
					toReturn.Parts = append(toReturn.Parts, part)
				}
			}
			sort.Sort(toReturn)
			return toReturn
		},
	})
	defs = append(defs, Definition{
		Name: "PadRight",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			list, n, x, valid := ValidatePadParams(this)
			if !valid {
				return this
			}
			toReturn := NewExpression([]Ex{list.Parts[0]})
			for i := int64(0); i < n; i++ {
				if i >= int64(len(list.Parts)-1) {
					toReturn.Parts = append(toReturn.Parts, x)
				} else {
					toReturn.Parts = append(toReturn.Parts, list.Parts[i+1])
				}
			}
			return toReturn
		},
	})
	defs = append(defs, Definition{
		Name: "PadLeft",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			list, n, x, valid := ValidatePadParams(this)
			if !valid {
				return this
			}
			toReturn := NewExpression([]Ex{list.Parts[0]})
			for i := int64(0); i < n; i++ {
				if i < n-int64(len(list.Parts))+1 {
					toReturn.Parts = append(toReturn.Parts, x)
				} else {
					listI := int64(len(list.Parts)) - (n - i)
					toReturn.Parts = append(toReturn.Parts, list.Parts[listI])
				}
			}
			return toReturn
		},
	})
	defs = append(defs, Definition{
		Name: "Range",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			// I should probably refactor the IterSpec system so that it does not
			// require being passed a list and a variable of iteration. TODO
			iterSpecList := NewExpression([]Ex{&Symbol{"System`List"}, &Symbol{"System`$DUMMY"}})
			iterSpecList.Parts = append(iterSpecList.Parts, this.Parts[1:]...)
			is, isOk := iterSpecFromList(es, iterSpecList)
			if !isOk {
				return this
			}
			toReturn := NewExpression([]Ex{&Symbol{"System`List"}})
			for is.cont() {
				toReturn.Parts = append(toReturn.Parts, is.getCurr())
				is.next()
			}
			return toReturn
		},
	})
	defs = append(defs, Definition{
		Name: "Part",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) == 1 {
				return this
			}
			applied, ok := this.Parts[1], true
			// This assumes that e[[a, b]] is equivalent to e[[a]][[b]]. It is
			// in most cases, but try this with mat[[All, 5]]. It seems that
			// the indices are aware of each other and the fact that e is a
			// matrix. I will most likely need to perform this selection using
			// another method. TODO
			for i := 2; i < len(this.Parts); i++ {
				//es.Infof("applyIndex(%v, %v)", applied, this.Parts[i])
				applied, ok = applyIndex(applied, this.Parts[i])
				//es.Infof("after running, applied = %v", applied)
				if !ok {
					return this
				}
			}
			return applied
		},
	})
	defs = append(defs, Definition{
		Name: "All",
	})
	defs = append(defs, Definition{
		Name: "Thread",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}
			expr, isExpr := this.Parts[1].(*Expression)
			if !isExpr {
				return this.Parts[1]
			}
			newExpr, _ := ThreadExpr(expr)
			return newExpr
		},
	})
	defs = append(defs, Definition{
		Name: "Append",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}
			expr, isExpr := this.Parts[1].(*Expression)
			if !isExpr {
				return this
			}
			res := NewExpression(append([]Ex{}, expr.Parts...))
			res.Parts = append(res.Parts, this.Parts[2])
			return res
		},
	})
	defs = append(defs, Definition{
		Name: "AppendTo",
	})
	defs = append(defs, Definition{
		Name: "Prepend",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}
			expr, isExpr := this.Parts[1].(*Expression)
			if !isExpr {
				return this
			}
			res := NewExpression([]Ex{expr.Parts[0]})
			res.Parts = append(res.Parts, this.Parts[2])
			res.Parts = append(res.Parts, expr.Parts[1:]...)
			return res
		},
	})
	defs = append(defs, Definition{
		Name: "PrependTo",
	})
	defs = append(defs, Definition{
		Name: "DeleteDuplicates",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}

			expr, isExpr := this.Parts[1].(*Expression)
			if isExpr {
				toReturn := NewExpression([]Ex{expr.Parts[0]})
				seen := map[uint64]bool{}
				for _, orig := range expr.Parts[1:] {
					hash := hashEx(orig)
					_, isDupe := seen[hash]
					if !isDupe {
						seen[hash] = true
						toReturn.Parts = append(toReturn.Parts, orig)
					}
				}
				return toReturn
			}
			return this
		},
	})
	defs = append(defs, Definition{
		Name: "Last",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}

			expr, isExpr := this.Parts[1].(*Expression)
			if isExpr {
				if len(expr.Parts) < 2 {
					return this
				}
				return expr.Parts[len(expr.Parts)-1]
			}
			return this
		},
	})
	defs = append(defs, Definition{
		Name: "Select",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}

			expr, isExpr := this.Parts[1].(*Expression)
			if isExpr {
				res := NewExpression([]Ex{expr.Parts[0]})
				for _, part := range expr.Parts[1:] {
					pass := (NewExpression([]Ex{
						this.Parts[2],
						part,
					})).Eval(es)
					passSymbol, passIsSymbol := pass.(*Symbol)
					if passIsSymbol {
						if passSymbol.Name == "System`True" {
							res.Parts = append(res.Parts, part)
						}
					}
				}
				return res
			}
			return this
		},
	})
	defs = append(defs, Definition{Name: "ListQ"})
	return
}
