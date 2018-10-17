package expreduce

import (
	"bytes"
	"math/big"
	"sort"
	"sync"

	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

func (this *Expression) ToStringList(params expreduceapi.ToStringParams) (bool, string) {
	if params.form == "FullForm" {
		return false, ""
	}
	var buffer bytes.Buffer
	if params.form == "TeXForm" {
		buffer.WriteString("\\left\\{")
	} else {
		buffer.WriteString("{")
	}
	for i, e := range this.Parts[1:] {
		params.previousHead = "<TOPLEVEL>"
		buffer.WriteString(e.StringForm(params))
		if i != len(this.Parts[1:])-1 {
			buffer.WriteString(",")
			if params.form != "TeXForm" {
				buffer.WriteString(" ")
			}
		}
	}
	if params.form == "TeXForm" {
		buffer.WriteString("\\right\\}")
	} else {
		buffer.WriteString("}")
	}
	return true, buffer.String()
}

func MemberQ(components []expreduceapi.Ex, item expreduceapi.Ex, es *expreduceapi.EvalStateInterface) bool {
	for _, part := range components {
		if matchq, _ := IsMatchQ(part, item, EmptyPD(), es); matchq {
			return true
		}
	}
	return false
}

func ValidatePadParams(this *expreduceapi.ExpressionInterface) (list *expreduceapi.ExpressionInterface, n int64, x expreduceapi.Ex, valid bool) {
	valid = false
	x = NewInteger(big.NewInt(0))
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

	list, listIsExpr := this.Parts[1].(*expreduceapi.ExpressionInterface)
	if !listIsExpr {
		return
	}

	valid = true
	return
}

func validateIndex(i expreduceapi.Ex, l int) (int64, bool) {
	iInt, iIsInt := i.(*Integer)
	if !iIsInt {
		return 0, false
	}
	if iInt.Val.Int64() >= int64(l) {
		return 0, false
	}
	// TODO: support this in the future.
	if iInt.Val.Int64() < 0 {
		return 0, false
	}
	return iInt.Val.Int64(), true
}

func applyIndex(ex expreduceapi.Ex, indices []expreduceapi.Ex, currDim int) (expreduceapi.Ex, bool) {
	// Base case
	if currDim >= len(indices) {
		return ex, true
	}
	expr, isExpr := ex.(*expreduceapi.ExpressionInterface)
	if !isExpr {
		return nil, false
	}

	// Singular selection
	if _, iIsInt := indices[currDim].(*Integer); iIsInt {
		indexVal, indexOk := validateIndex(indices[currDim], len(expr.Parts))
		if !indexOk {
			return nil, false
		}
		return applyIndex(expr.Parts[indexVal], indices, currDim+1)
	}

	// Range selections
	rangeMin, rangeMax, rangeOk := int64(0), int64(0), false
	if iSpan, iIsSpan := HeadAssertion(indices[currDim], "System`Span"); iIsSpan {
		if len(iSpan.Parts) != 3 {
			return nil, false
		}
		start, startOk := validateIndex(iSpan.Parts[1], len(expr.Parts)+1)
		end, endOk := validateIndex(iSpan.Parts[2], len(expr.Parts))
		if endSym, endIsSym := iSpan.Parts[2].(*Symbol); endIsSym {
			if endSym.Name == "System`All" {
				end, endOk = int64(len(expr.Parts)-1), true
			}
		}
		if !startOk || !endOk {
			return nil, false
		}
		rangeMin, rangeMax, rangeOk = start, end, true
	}
	iSym, iIsSym := indices[currDim].(*Symbol)
	if iIsSym {
		if iSym.Name == "System`All" {
			rangeMin, rangeMax, rangeOk = 1, int64(len(expr.Parts)-1), true
		}
	}
	if rangeOk {
		toReturn := E(expr.Parts[0])
		for i := rangeMin; i <= rangeMax; i++ {
			applied, appOk := applyIndex(expr.Parts[i], indices, currDim+1)
			if !appOk {
				return nil, false
			}
			toReturn.appendEx(applied)
		}
		return toReturn, true
	}
	return nil, false
}

func ThreadExpr(expr *expreduceapi.ExpressionInterface) (*expreduceapi.ExpressionInterface, bool) {
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
	toReturn := NewExpression([]expreduceapi.Ex{NewSymbol("System`List")})
	for listI := 0; listI < listLen; listI++ {
		thisExpr := NewExpression([]expreduceapi.Ex{expr.Parts[0].DeepCopy()})
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

func countFunctionLevelSpec(pattern expreduceapi.Ex, e expreduceapi.Ex, partList []int64, generated *int64, es *expreduceapi.EvalStateInterface) expreduceapi.Ex {
	if isMatch, _ := IsMatchQ(e, pattern, EmptyPD(), es); isMatch {
		*generated++
	}
	return e
}

func GetListDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name:     "List",
		toString: (*expreduceapi.ExpressionInterface).ToStringList,
	})
	defs = append(defs, Definition{
		Name: "Total",
	})
	defs = append(defs, Definition{
		Name: "Mean",
	})
	defs = append(defs, Definition{
		Name: "Table",
		legacyEvalFn: func(this *expreduceapi.ExpressionInterface, es *expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.Parts) >= 3 {
				mis, isOk := multiIterSpecFromLists(es, this.Parts[2:])
				if isOk {
					// Simulate evaluation within Block[]
					mis.takeVarSnapshot(es)
					toReturn := NewExpression([]expreduceapi.Ex{NewSymbol("System`List")})
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
		Name: "ParallelTable",
		legacyEvalFn: func(this *expreduceapi.ExpressionInterface, es *expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.Parts) >= 3 {
				mis, isOk := multiIterSpecFromLists(es, this.Parts[2:])
				if isOk {
					// Simulate evaluation within Block[]
					toReturn := NewExpression([]expreduceapi.Ex{NewSymbol("System`List")})
					for mis.cont() {
						toReturn.Parts = append(toReturn.Parts, ReplacePD(this.Parts[1].DeepCopy(), es, mis.currentPDManager()))
						es.Debugf("%v\n", toReturn)
						mis.next()
					}
					var wg sync.WaitGroup
					for i := 1; i < len(toReturn.Parts); i++ {
						wg.Add(1)
						go func(idx int) {
							defer wg.Done()
							toReturn.Parts[idx] = toReturn.Parts[idx].Eval(es)
						}(i)
					}
					wg.Wait()
					return toReturn
				}
			}
			return this
		},
	})
	defs = append(defs, Definition{
		Name: "MemberQ",
		legacyEvalFn: func(this *expreduceapi.ExpressionInterface, es *expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.Parts) != 3 {
				return this
			}
			expr, isExpr := this.Parts[1].(*expreduceapi.ExpressionInterface)
			if isExpr {
				if MemberQ(expr.Parts[1:], this.Parts[2], es) {
					return NewSymbol("System`True")
				}
			}
			return NewSymbol("System`False")
		},
	})
	defs = append(defs, Definition{
		Name: "Cases",
		legacyEvalFn: func(this *expreduceapi.ExpressionInterface, es *expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.Parts) != 3 {
				return this
			}

			expr, isExpr := this.Parts[1].(*expreduceapi.ExpressionInterface)
			if isExpr {
				toReturn := NewExpression([]expreduceapi.Ex{NewSymbol("System`List")})
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
		legacyEvalFn: func(this *expreduceapi.ExpressionInterface, es *expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.Parts) != 3 {
				return this
			}

			expr, isExpr := this.Parts[1].(*expreduceapi.ExpressionInterface)
			if isExpr {
				toReturn := NewExpression([]expreduceapi.Ex{expr.Parts[0]})
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
		legacyEvalFn: func(this *expreduceapi.ExpressionInterface, es *expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.Parts) == 1 {
				return NewExpression([]expreduceapi.Ex{NewSymbol("System`List")})
			}
			var firstHead expreduceapi.Ex = nil
			var allParts *expreduceapi.ExpressionInterface = nil
			for _, part := range this.Parts[1:] {
				expr, isExpr := part.(*expreduceapi.ExpressionInterface)
				if !isExpr {
					return this
				}
				if firstHead == nil {
					firstHead = expr.Parts[0]
					allParts = NewExpression([]expreduceapi.Ex{firstHead})
				} else if !IsSameQ(firstHead, expr.Parts[0], &es.CASLogger) {
					return this
				}
				allParts.Parts = append(allParts.Parts, expr.Parts[1:]...)
			}
			sort.Sort(allParts)
			toReturn := NewExpression([]expreduceapi.Ex{firstHead})
			var lastEx expreduceapi.Ex = nil
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
		legacyEvalFn: func(this *expreduceapi.ExpressionInterface, es *expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.Parts) == 1 {
				return this
			}
			var firstHead expreduceapi.Ex = nil
			exclusions := map[uint64]bool{}
			for _, part := range this.Parts[1:] {
				expr, isExpr := part.(*expreduceapi.ExpressionInterface)
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
			toReturn := NewExpression([]expreduceapi.Ex{firstHead})
			added := map[uint64]bool{}
			for _, part := range this.Parts[1].(*expreduceapi.ExpressionInterface).Parts[1:] {
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
		legacyEvalFn: func(this *expreduceapi.ExpressionInterface, es *expreduceapi.EvalStateInterface) expreduceapi.Ex {
			list, n, x, valid := ValidatePadParams(this)
			if !valid {
				return this
			}
			toReturn := NewExpression([]expreduceapi.Ex{list.Parts[0]})
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
		legacyEvalFn: func(this *expreduceapi.ExpressionInterface, es *expreduceapi.EvalStateInterface) expreduceapi.Ex {
			list, n, x, valid := ValidatePadParams(this)
			if !valid {
				return this
			}
			toReturn := NewExpression([]expreduceapi.Ex{list.Parts[0]})
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
		legacyEvalFn: func(this *expreduceapi.ExpressionInterface, es *expreduceapi.EvalStateInterface) expreduceapi.Ex {
			// I should probably refactor the IterSpec system so that it does not
			// require being passed a list and a variable of iteration. TODO
			iterSpecList := NewExpression([]expreduceapi.Ex{NewSymbol("System`List"), NewSymbol("System`$DUMMY")})
			iterSpecList.Parts = append(iterSpecList.Parts, this.Parts[1:]...)
			is, isOk := iterSpecFromList(es, iterSpecList)
			if !isOk {
				return this
			}
			toReturn := NewExpression([]expreduceapi.Ex{NewSymbol("System`List")})
			for is.cont() {
				toReturn.Parts = append(toReturn.Parts, is.getCurr())
				is.next()
			}
			return toReturn
		},
	})
	defs = append(defs, Definition{
		Name: "Part",
		legacyEvalFn: func(this *expreduceapi.ExpressionInterface, es *expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.Parts) == 1 {
				return this
			}
			applied, ok := applyIndex(this.Parts[1], this.Parts[2:], 0)
			if !ok {
				return this
			}
			return applied
		},
	})
	defs = append(defs, Definition{Name: "Span"})
	defs = append(defs, Definition{Name: "All"})
	defs = append(defs, Definition{
		Name: "Thread",
		legacyEvalFn: func(this *expreduceapi.ExpressionInterface, es *expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.Parts) != 2 {
				return this
			}
			expr, isExpr := this.Parts[1].(*expreduceapi.ExpressionInterface)
			if !isExpr {
				return this.Parts[1]
			}
			newExpr, _ := ThreadExpr(expr)
			return newExpr
		},
	})
	defs = append(defs, Definition{
		Name: "Append",
		legacyEvalFn: func(this *expreduceapi.ExpressionInterface, es *expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.Parts) != 3 {
				return this
			}
			expr, isExpr := this.Parts[1].(*expreduceapi.ExpressionInterface)
			if !isExpr {
				return this
			}
			res := NewExpression(append([]expreduceapi.Ex{}, expr.Parts...))
			res.Parts = append(res.Parts, this.Parts[2])
			return res
		},
	})
	defs = append(defs, Definition{
		Name: "AppendTo",
	})
	defs = append(defs, Definition{
		Name: "Prepend",
		legacyEvalFn: func(this *expreduceapi.ExpressionInterface, es *expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.Parts) != 3 {
				return this
			}
			expr, isExpr := this.Parts[1].(*expreduceapi.ExpressionInterface)
			if !isExpr {
				return this
			}
			res := NewExpression([]expreduceapi.Ex{expr.Parts[0]})
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
		legacyEvalFn: func(this *expreduceapi.ExpressionInterface, es *expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.Parts) != 2 {
				return this
			}

			expr, isExpr := this.Parts[1].(*expreduceapi.ExpressionInterface)
			if isExpr {
				toReturn := NewExpression([]expreduceapi.Ex{expr.Parts[0]})
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
		Name: "Select",
		legacyEvalFn: func(this *expreduceapi.ExpressionInterface, es *expreduceapi.EvalStateInterface) expreduceapi.Ex {
			maxN := MaxInt64
			if len(this.Parts) == 4 {
				if asInt, isInt := this.Parts[3].(*Integer); isInt {
					maxN = asInt.Val.Int64()
					if maxN < 0 {
						return this
					}
				} else {
					return this
				}
			} else if len(this.Parts) != 3 {
				return this
			}

			expr, isExpr := this.Parts[1].(*expreduceapi.ExpressionInterface)
			if isExpr {
				res := NewExpression([]expreduceapi.Ex{expr.Parts[0]})
				added := int64(0)
				for _, part := range expr.Parts[1:] {
					if added >= maxN {
						break
					}
					pass := (NewExpression([]expreduceapi.Ex{
						this.Parts[2],
						part,
					})).Eval(es)
					passSymbol, passIsSymbol := pass.(*Symbol)
					if passIsSymbol {
						if passSymbol.Name == "System`True" {
							res.Parts = append(res.Parts, part)
							added += 1
						}
					}
				}
				return res
			}
			return this
		},
	})
	defs = append(defs, Definition{
		Name: "Scan",
		legacyEvalFn: func(this *expreduceapi.ExpressionInterface, es *expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.Parts) != 3 {
				return this
			}

			expr, isExpr := this.Parts[2].(*expreduceapi.ExpressionInterface)
			if !isExpr {
				return this
			}
			for _, part := range expr.Parts[1:] {
				res := (NewExpression([]expreduceapi.Ex{
					this.Parts[1],
					part,
				})).Eval(es)
				if es.HasThrown() {
					return es.thrown
				}
				if asReturn, isReturn := HeadAssertion(res, "System`Return"); isReturn {
					if len(asReturn.Parts) < 2 {
						return NewSymbol("System`Null")
					}
					return asReturn.Parts[1]
				}
			}
			return NewSymbol("System`Null")
		},
	})
	defs = append(defs, Definition{
		Name: "Join",
		legacyEvalFn: func(this *expreduceapi.ExpressionInterface, es *expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.Parts) <= 1 {
				return NewHead("System`List")
			}

			res := NewEmptyExpression()
			for _, part := range this.Parts[1:] {
				expr, isExpr := part.(*expreduceapi.ExpressionInterface)
				if !isExpr {
					return this
				}
				if len(res.Parts) == 0 {
					res.appendExArray(expr.Parts)
				} else {
					if !IsSameQ(expr.Parts[0], res.Parts[0], &es.CASLogger) {
						return this
					}
					res.appendExArray(expr.Parts[1:])
				}
			}
			return res
		},
	})
	defs = append(defs, Definition{Name: "ListQ"})
	defs = append(defs, Definition{Name: "Last"})
	defs = append(defs, Definition{Name: "First"})
	defs = append(defs, Definition{Name: "Rest"})
	defs = append(defs, Definition{
		Name: "Count",
		legacyEvalFn: levelSpecFunction(
			countFunctionLevelSpec,
			unoptimizedSimpleLevelSpec,
			true,
			true,
		),
	})
	defs = append(defs, Definition{Name: "Tally"})
	defs = append(defs, Definition{Name: "ConstantArray"})
	defs = append(defs, Definition{
		Name: "Reverse",
		legacyEvalFn: func(this *expreduceapi.ExpressionInterface, es *expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.Parts) != 2 {
				return this
			}
			expr, isExpr := this.Parts[1].(*expreduceapi.ExpressionInterface)
			if !isExpr {
				return this
			}
			res := NewExpression([]expreduceapi.Ex{expr.Parts[0]})
			for i := len(expr.Parts) - 1; i > 0; i-- {
				res.Parts = append(res.Parts, expr.Parts[i])
			}
			return res
		},
	})
	return
}
