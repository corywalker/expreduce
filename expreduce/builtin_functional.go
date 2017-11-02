package expreduce

import (
	"math/big"
)

//The following functions help to interpret the Ex interface, they could probably be moved
//to another file since they are useful in many common situations

func parseInteger(part Ex) (value int64, isInteger bool) {
	integer, isInteger := part.(*Integer)
	if isInteger {
		return integer.Val.Int64(), true
	} else {
		return 0, false
	}
}

func parseFloat(part Ex) (value float64, isFloat bool) {
	float, isFloat := part.(*Flt)
	if isFloat {
		value, _ := float.Val.Float64()
		return value, true
	} else {
		return 0, false
	}
}

func parseExpression(part Ex) (expression *Expression, isExpression bool) {
	expression, isExpression = part.(*Expression)
	return expression, isExpression
}

func parseSymbol(part Ex) (symbol *Symbol, isSymbol bool) {
	symbol, isSymbol = part.(*Symbol)
	return symbol, isSymbol
}

func parseInfinity(part Ex, es *EvalState) bool {
	symbol, isSymbol := parseSymbol(part)
	if isSymbol {
		return symbol.IsEqual(NewSymbol("System`Infinity"), &es.CASLogger) == "EQUAL_TRUE"
	}
	return false
}

func parseNegativeInfinity(part Ex, es *EvalState) bool {
	expr, isExpr := parseExpression(part)
	if isExpr {
		template := NewExpression([]Ex{
			NewSymbol("System`Times"),
			NewInt(-1),
			NewSymbol("System`Infinity"),
		})
		return expr.IsEqual(template, &es.CASLogger) == "EQUAL_TRUE"
	}
	return false
}

// The levelSpec struct is used to work with level specifications
type levelSpec struct {
	isMinDepth	bool	//If the min specification represents a depth (as opposed to level)
	isMaxDepth	bool	//If the max specification represents a depth (as opposed to level)
	min			int64
	max			int64
	valid		bool
}

func (spec levelSpec) isLevel() (bool, bool) {
	return !spec.isMinDepth, !spec.isMaxDepth
}

func (spec levelSpec) isDepth() (bool, bool) {
	return spec.isMinDepth, spec.isMaxDepth
}

func (spec levelSpec) isValid() bool {
	return spec.valid
}

func (spec levelSpec) checkLevel(level int64) bool {
	switch {
	case !spec.isMinDepth && !spec.isMaxDepth:
		return level >= spec.min && level <= spec.max
	case !spec.isMinDepth && spec.isMaxDepth:
		return level >= spec.min
	case spec.isMinDepth && !spec.isMaxDepth:
		return level <= spec.max
	}

	return true
}

func (spec levelSpec) checkDepth(depth int64) bool {
	switch {
	case spec.isMinDepth && spec.isMaxDepth:
		return depth <= spec.min && depth >= spec.max
	case spec.isMinDepth && !spec.isMaxDepth:
		return depth <= spec.min
	case !spec.isMinDepth && spec.isMaxDepth:
		return depth >= spec.max
	}

	return true
}

// Levels can be specified in the form n, {n}, {n1, n2}, Infinity, -Infinity
// n, n1, n2 are integers which can be positive or negative
func parseLevelSpec(this Ex, es *EvalState) levelSpec{
	integer, isInteger := parseInteger(this)
	expression, isExpression := parseExpression(this)
	isInfinity := parseInfinity(this, es)
	isNegativeInfinity := parseNegativeInfinity(this, es)

	//These are the maximum and minimum numbers which are representable in
	//the int64 data type
	const inf int64 = 1<<31 - 1 //Same but with 63 does not work for some reason
	const ninf int64 = -1 << 31

	//If it's a symbol, deal with it
	//If it's not an accepted symbol and not an expression, return false
	switch {
	case isInteger:
		if integer < 0 {
			return levelSpec{false, true, 1, -integer, true}
		} else {
			return levelSpec{false, false, 1, integer, true}
		}
	case isInfinity:
		return levelSpec{false, false, 1, inf, true}
	case isNegativeInfinity:
		return levelSpec{false, true, 1, inf, true}
	case !isExpression:
		return levelSpec{false, false, 1, 1, false}
	}

	//If the head of the expression is not List, return false
	expression, isList := headExAssertion(expression, NewSymbol("System`List"), &es.CASLogger)
	if !isList {
		return levelSpec{false, false, 1, 1, false}
	}

	//Handle case where the list has only one element
	if len(expression.Parts) == 2 {
		integer, isInteger = parseInteger(expression.Parts[1])
		isInfinity := parseInfinity(expression.Parts[1], es)
		isNegativeInfinity := parseNegativeInfinity(expression.Parts[1], es)

		switch {
		case isInteger:
			if integer < 0 {
				return levelSpec{true, true, -integer, -integer, true}
			} else {
				return levelSpec{false, false, integer, integer, true}
			}
		case isInfinity:
			return levelSpec{false, false, inf, inf, true}
		case isNegativeInfinity:
			return levelSpec{true, true, inf, inf, true}
		}
	}

	//Handle case where the list has two elements
	if len(expression.Parts) == 3 {
		integer1, isInteger1 := parseInteger(expression.Parts[1])
		integer2, isInteger2 := parseInteger(expression.Parts[2])

		isInfinity1 := parseInfinity(expression.Parts[1], es)
		if isInfinity1 {
			integer1 = inf
			isInteger1 = true
		}

		isInfinity2 := parseInfinity(expression.Parts[2], es)
		if isInfinity2 {
			integer2 = inf
			isInteger2 = true
		}

		isNegativeInfinity1 := parseNegativeInfinity(expression.Parts[1], es)
		if isNegativeInfinity1 {
			integer1 = ninf
			isInteger1 = true
		}

		isNegativeInfinity2 := parseNegativeInfinity(expression.Parts[2], es)
		if isNegativeInfinity2 {
			integer2 = ninf
			isInteger2 = true
		}

		if isInteger1 && isInteger2 {
			switch {
			case integer1 >= 0 && integer2 >= 0:
				return levelSpec{false, false, integer1, integer2, true}
			case integer1 < 0 && integer2 < 0:
				return levelSpec{true, true, -integer1, -integer2, true}
			case integer1 < 0 && integer2 >= 0:
				return levelSpec{true, false, -integer1, integer2, true}
			case integer1 >= 0 && integer2 < 0:
				return levelSpec{false, true, integer1, -integer2, true}
			}
		}
	}

	//If the function has not returned by now then the specification is invalid
	return levelSpec{false, false, 1, 1, false}
}

//This is an optimization with regards to expressionWalkMapBackwards which only deals with level specification,
//expressionWalkMapBackwards also deals with depths, but has to visit the entire expression tree.
func expressionWalkMap(f func(Ex, Ex, []int64) Ex, head Ex, partSpec[]int64, this *Expression, es *EvalState, spec levelSpec) *Expression {
	toReturn := NewExpression([]Ex{this.Parts[0]})

	for i, expr := range this.Parts[1:] {
		newExpression := expr

		//Keep track of which part in the full expression this corresponds to
		currentPartSpec := append(partSpec, int64(i+1))
		level := int64(len(currentPartSpec))

		//If this part is nonatomic and its level is covered by the level specification,
		//apply expressionWalkMap recursively
		expression, isExpression := newExpression.(*Expression)
		if isExpression && level < spec.max {
			newExpression = expressionWalkMap(f, head, currentPartSpec, expression, es, spec)
		}

		//If this part is covered by the level specification, apply the function
		//specified by the first argument of Map
		if level >= spec.min {
			newExpression = f(head, newExpression, currentPartSpec)
			toReturn.Parts = append(toReturn.Parts, newExpression)
		} else {
			toReturn.Parts = append(toReturn.Parts, newExpression)
		}
	}

	return toReturn
}

func expressionWalkMapBackwards(f func(Ex, Ex, []int64) Ex, head Ex, partSpec[]int64, this *Expression, es *EvalState, spec levelSpec) (*Expression, int64) {
	toReturn := NewExpression([]Ex{this.Parts[0]})
	currentMaxDepth := int64(1)

	for i, expr := range this.Parts[1:] {
		newExpression := expr
		depth := int64(0)

		currentPartSpec := append(partSpec, int64(i+1))
		level := int64(len(currentPartSpec))

		expression, isExpression := newExpression.(*Expression)
		if isExpression {
			//Determine the depth of this part
			newExpression, depth = expressionWalkMapBackwards(f, head, currentPartSpec, expression, es, spec)
			if depth > currentMaxDepth {
				currentMaxDepth = depth
			}

			if spec.checkLevel(level) && spec.checkDepth(depth) {
				newExpression = f(head, newExpression, currentPartSpec)
				toReturn.Parts = append(toReturn.Parts, newExpression)
			} else {
				toReturn.Parts = append(toReturn.Parts, newExpression)
			}
		} else { //If the node is atomic
			level = level+1
			depth = int64(1)

			if spec.checkLevel(level) && spec.checkDepth(depth) {
				newExpression = f(head, expr, currentPartSpec)
				toReturn.Parts = append(toReturn.Parts, newExpression)
			} else {
				toReturn.Parts = append(toReturn.Parts, newExpression)
			}
		}
	}

	return toReturn, currentMaxDepth+1
}

func wrapWithHead(head Ex, expr Ex, partList []int64) Ex {
	return NewExpression([]Ex{head, expr})
}

func wrapWithHeadIndexed(head Ex, expr Ex, partList []int64) Ex {
	partSpec := []Ex{NewSymbol("System`List")}
	for _, part := range partList {
		partSpec = append(partSpec, NewInt(part))
	}
	partSpecExpr :=  NewExpression(partSpec)
	return NewExpression([]Ex{head, expr, partSpecExpr})
}

func applyHead(head Ex, expr Ex, partList []int64) Ex {
	expression, isExpr := expr.(*Expression)
	if !isExpr {
		return expr
	}
	toReturn := NewExpression([]Ex{head})
	toReturn.Parts = append(toReturn.Parts, expression.Parts[1:]...)
	return toReturn
}

func mapFunction(f func(Ex, Ex, []int64) Ex, isApply bool) func(*Expression, *EvalState) Ex {
	return func(this *Expression, es *EvalState) Ex {
		// Optimization of the very common case where Map has two arguments
		if len(this.Parts) == 3 {
			if !isApply{
				expr, isExpr := this.Parts[2].(*Expression)
				if isExpr {
					toReturn := NewExpression([]Ex{expr.Parts[0]})
					for i := 1; i < len(expr.Parts); i++ {
						toReturn.Parts = append(toReturn.Parts, NewExpression([]Ex{
							this.Parts[1],
							expr.Parts[i],
						}))
					}
					return toReturn
				}
				return this.Parts[2]
			} else {
				sym, isSym := this.Parts[1].(*Symbol)
				expr, isExpr := this.Parts[2].(*Expression)
				if isSym && isExpr {
					toReturn := NewExpression([]Ex{sym})
					toReturn.Parts = append(toReturn.Parts, expr.Parts[1:]...)
					return toReturn.Eval(es)
				}
				return this.Parts[2]
			}
		}

		if len(this.Parts) != 4 {
			return this
		}

		spec := parseLevelSpec(this.Parts[3], es)
		if !spec.isValid() {
			return this
		}

		//If the second argument is atomic, it will be ignored except in one case
		expression, nonAtomic := this.Parts[2].(*Expression)
		if !nonAtomic {
			if spec.checkLevel(0) && spec.checkDepth(0) {
				return f(this.Parts[1], this.Parts[2], []int64{})
			} else {
				return this.Parts[2]
			}
		}

		if spec.min == 0 && spec.max == 0 {
			return f(this.Parts[1], this.Parts[2], []int64{})
		}

		//In this special case we do not have to keep track of depth, this can be computed faster
		//than when depth is required because we do not always have to recurse all the way to the
		//bottom of the expression
		if !spec.isMinDepth && !spec.isMaxDepth {
			newExpression := expressionWalkMap(f, this.Parts[1], []int64{}, expression, es, spec)

			if spec.checkLevel(0) && spec.checkDepth(0) {
				return f(this.Parts[1], newExpression, []int64{})
			} else {
				return newExpression
			}
		}

		//We now turn to the most general case, where levels can be specified as either
		//positive or negative integers, where negative integers denote depth rather than level
		newExpression, depth := expressionWalkMapBackwards(f, this.Parts[1], []int64{}, expression, es, spec)

		//Whether to wrap the zeroth level with the function.
		if spec.checkLevel(0) && spec.checkDepth(depth) {
			return f(this.Parts[1], newExpression, []int64{})
		} else {
			return newExpression
		}
	}
}


func getFunctionalDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "Function",
	})
	defs = append(defs, Definition{
		Name: "Slot",
	})
	defs = append(defs, Definition{
		Name: "Apply",
		/*legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}

			sym, isSym := this.Parts[1].(*Symbol)
			expr, isExpr := this.Parts[2].(*Expression)
			if isSym && isExpr {
				toReturn := NewExpression([]Ex{sym})
				toReturn.Parts = append(toReturn.Parts, expr.Parts[1:]...)
				return toReturn.Eval(es)
			}
			return this.Parts[2]
		},*/
		legacyEvalFn: mapFunction(applyHead, true),
	})
	defs = append(defs, Definition{
		Name: "Map",
		legacyEvalFn: mapFunction(wrapWithHead, false),
	})

	defs = append(defs, Definition{
		Name: "MapIndexed",
		legacyEvalFn: mapFunction(wrapWithHeadIndexed, false),
	})

	defs = append(defs, Definition{
		Name: "FoldList",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 4 {
				return this
			}

			f := this.Parts[1]
			first := this.Parts[2]
			values, nonAtomic := this.Parts[3].(*Expression)

			if !nonAtomic {
				return this
			}

			toReturn := NewExpression([]Ex{values.Parts[0], first})

			if len(values.Parts) < 2 {
				return toReturn
			}

			expr := NewExpression([]Ex{
				f,
				first,
				values.Parts[1],
			})

			toReturn.Parts = append(toReturn.Parts, expr)

			for i := 2; i < len(values.Parts); i++ {
				expr = NewExpression([]Ex{
					f,
					expr,
					values.Parts[i],
				})

				toReturn.Parts = append(toReturn.Parts, expr)
			}

			return toReturn
		},
	})
	defs = append(defs, Definition{Name: "Fold"})

	defs = append(defs, Definition{
		Name: "NestList",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 4 {
				return this
			}

			f := this.Parts[1]
			expr := this.Parts[2]
			nInt, isInteger := this.Parts[3].(*Integer)
			if !isInteger {
				return this
			}
			n := nInt.Val.Int64()
			if n < 0 {
				return this
			}

			toReturn := NewExpression([]Ex{NewSymbol("System`List"), expr})

			for i := int64(1); i <= n; i++ {
				expr = NewExpression([]Ex{
					f,
					expr,
				})

				toReturn.Parts = append(toReturn.Parts, expr)
			}

			return toReturn
		},
	})

	defs = append(defs, Definition{Name: "Nest"})
	defs = append(defs, Definition{
		Name: "NestWhileList",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) < 4 || len(this.Parts) > 7 {
				return this
			}

			f := this.Parts[1]
			expr := this.Parts[2]
			test := this.Parts[3]

			m := int64(1)
			if len(this.Parts) > 4 {
				mInt, isInteger := this.Parts[4].(*Integer)
				mSymbol, isSymbol := this.Parts[4].(*Symbol)
				if isInteger {
					m = mInt.Val.Int64()
					if m < 0 {
						return this
					}
				} else if isSymbol {
					if mSymbol.IsEqual(NewSymbol("System`All"), &es.CASLogger) == "EQUAL_TRUE" {
						m = -1
					} else {
						return this
					}
				} else {
					return this
				}
			}

			max := int64(-1)
			if len(this.Parts) > 5 {
				maxInt, isInteger := this.Parts[5].(*Integer)
				maxSymbol, isSymbol := this.Parts[5].(*Symbol)
				if isInteger {
					max = maxInt.Val.Int64()
					if maxInt.Val.Int64() < 0 {
						return this
					}
				} else if isSymbol {
					if maxSymbol.IsEqual(NewSymbol("System`Infinity"), &es.CASLogger) == "EQUAL_TRUE" {
						max = -1
					} else {
						return this
					}
				} else {
					return this
				}
			}

			n := int64(0)
			if len(this.Parts) > 6 {
				bonusIterationsInt, isInteger := this.Parts[6].(*Integer)
				if isInteger && bonusIterationsInt.Val.Int64() >= int64(0) {
					n = bonusIterationsInt.Val.Int64()
				}
			}

			evaluated := []Ex{expr.DeepCopy().Eval(es)}
			toReturn := NewExpression([]Ex{NewSymbol("System`List"), expr})

			isequal := "EQUAL_TRUE"
			cont := isequal == "EQUAL_TRUE"
			for i := int64(2); cont; i++ {
				expr = NewExpression([]Ex{
					f,
					expr,
				})
				toReturn.Parts = append(toReturn.Parts, expr)
				evaluated = append(evaluated, expr.DeepCopy().Eval(es)) // Could use a stack of length m

				if i >= m {
					testExpression := NewExpression([]Ex{test})
					if m >= 0 {
						testExpression.Parts = append(testExpression.Parts, evaluated[int64(len(evaluated))-m:]...)
					} else {
						testExpression.Parts = append(testExpression.Parts, evaluated...)
					}
					isequal = testExpression.Eval(es).IsEqual(NewSymbol("System`True"), &es.CASLogger)
					cont = isequal == "EQUAL_TRUE"
				}

				if i > max && max != -1 {
					cont = false
				}
			}

			if n > 0 {
				for i := int64(0); i < n; i++ {
					expr = NewExpression([]Ex{
						f,
						expr,
					})
					toReturn.Parts = append(toReturn.Parts, expr)
				}
			} else {
				toReturn.Parts = toReturn.Parts[:int64(len(toReturn.Parts))+n]
			}

			return toReturn
		},
	})
	defs = append(defs, Definition{Name: "NestWhile"})
	defs = append(defs, Definition{Name: "FixedPointList"})
	defs = append(defs, Definition{Name: "FixedPoint"})
	defs = append(defs, Definition{
		Name: "Array",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}

			nInt, nOk := this.Parts[2].(*Integer)
			if nOk {
				n := nInt.Val.Int64()
				toReturn := NewExpression([]Ex{NewSymbol("System`List")})
				for i := int64(1); i <= n; i++ {
					toReturn.Parts = append(toReturn.Parts, NewExpression([]Ex{
						this.Parts[1],
						NewInteger(big.NewInt(i)),
					}))
				}
				return toReturn
			}
			return this.Parts[2]
		},
	})
	defs = append(defs, Definition{
		Name: "Identity",
	})
	return
}
