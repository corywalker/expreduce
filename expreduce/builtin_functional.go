package expreduce

import (
	"math/big"

	"github.com/corywalker/expreduce/expreduce/atoms"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

//The following functions help to interpret the Ex interface, they could probably be moved
//to another file since they are useful in many common situations

func parseInteger(part expreduceapi.Ex) (value int64, isInteger bool) {
	integer, isInteger := part.(*atoms.Integer)
	if isInteger {
		return integer.Val.Int64(), true
	}
	return 0, false
}

func parseExpression(
	part expreduceapi.Ex,
) (expression expreduceapi.ExpressionInterface, isExpression bool) {
	expression, isExpression = part.(expreduceapi.ExpressionInterface)
	return expression, isExpression
}

func parseSymbol(part expreduceapi.Ex) (symbol *atoms.Symbol, isSymbol bool) {
	symbol, isSymbol = part.(*atoms.Symbol)
	return symbol, isSymbol
}

func parseInfinity(
	part expreduceapi.Ex,
	es expreduceapi.EvalStateInterface,
) bool {
	symbol, isSymbol := parseSymbol(part)
	if isSymbol {
		return symbol.IsEqual(
			atoms.NewSymbol("System`Infinity"),
		) == "EQUAL_TRUE"
	}
	return false
}

func parseNegativeInfinity(
	part expreduceapi.Ex,
	es expreduceapi.EvalStateInterface,
) bool {
	expr, isExpr := parseExpression(part)
	if isExpr {
		template := atoms.NewExpression([]expreduceapi.Ex{
			atoms.NewSymbol("System`Times"),
			atoms.NewInt(-1),
			atoms.NewSymbol("System`Infinity"),
		})

		return expr.IsEqual(template) == "EQUAL_TRUE"
	}
	return false
}

// The levelSpec struct is used to work with level specifications
type levelSpec struct {
	isMinDepth bool //If the min specification represents a depth (as opposed to level)
	isMaxDepth bool //If the max specification represents a depth (as opposed to level)
	min        int64
	max        int64
	valid      bool
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
func parseLevelSpec(
	this expreduceapi.Ex,
	es expreduceapi.EvalStateInterface,
) levelSpec {
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
		}
		return levelSpec{false, false, 1, integer, true}
	case isInfinity:
		return levelSpec{false, false, 1, inf, true}
	case isNegativeInfinity:
		return levelSpec{false, true, 1, inf, true}
	case !isExpression:
		return levelSpec{false, false, 1, 1, false}
	}

	//If the head of the expression is not List, return false
	expression, isList := atoms.HeadExAssertion(
		expression,
		atoms.NewSymbol("System`List"),
		es.GetLogger(),
	)
	if !isList {
		return levelSpec{false, false, 1, 1, false}
	}

	//Handle case where the list has only one element
	if len(expression.GetParts()) == 2 {
		integer, isInteger = parseInteger(expression.GetParts()[1])
		isInfinity := parseInfinity(expression.GetParts()[1], es)
		isNegativeInfinity := parseNegativeInfinity(
			expression.GetParts()[1],
			es,
		)

		switch {
		case isInteger:
			if integer < 0 {
				return levelSpec{true, true, -integer, -integer, true}
			}
			return levelSpec{false, false, integer, integer, true}
		case isInfinity:
			return levelSpec{false, false, inf, inf, true}
		case isNegativeInfinity:
			return levelSpec{true, true, inf, inf, true}
		}
	}

	//Handle case where the list has two elements
	if len(expression.GetParts()) == 3 {
		integer1, isInteger1 := parseInteger(expression.GetParts()[1])
		integer2, isInteger2 := parseInteger(expression.GetParts()[2])

		isInfinity1 := parseInfinity(expression.GetParts()[1], es)
		if isInfinity1 {
			integer1 = inf
			isInteger1 = true
		}

		isInfinity2 := parseInfinity(expression.GetParts()[2], es)
		if isInfinity2 {
			integer2 = inf
			isInteger2 = true
		}

		isNegativeInfinity1 := parseNegativeInfinity(
			expression.GetParts()[1],
			es,
		)
		if isNegativeInfinity1 {
			integer1 = ninf
			isInteger1 = true
		}

		isNegativeInfinity2 := parseNegativeInfinity(
			expression.GetParts()[2],
			es,
		)
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

// This is an optimization with regards to expressionWalkMapBackwards which only deals with level specification,
// expressionWalkMapBackwards also deals with depths, but has to visit the entire expression tree.
func expressionWalkMap(
	f func(expreduceapi.Ex, expreduceapi.Ex, []int64, *int64, expreduceapi.EvalStateInterface) expreduceapi.Ex,
	head expreduceapi.Ex,
	partSpec []int64,
	this expreduceapi.ExpressionInterface,
	es expreduceapi.EvalStateInterface,
	spec levelSpec,
	generated *int64,
) expreduceapi.ExpressionInterface {
	toReturn := atoms.NewExpression([]expreduceapi.Ex{this.GetParts()[0]})

	for i, expr := range this.GetParts()[1:] {
		newExpression := expr

		//Keep track of which part in the full expression this corresponds to
		currentPartSpec := append(partSpec, int64(i+1))
		level := int64(len(currentPartSpec))

		//If this part is nonatomic and its level is covered by the level specification,
		//apply expressionWalkMap recursively
		expression, isExpression := newExpression.(expreduceapi.ExpressionInterface)
		if isExpression && level < spec.max {
			newExpression = expressionWalkMap(
				f,
				head,
				currentPartSpec,
				expression,
				es,
				spec,
				generated,
			)
		}

		//If this part is covered by the level specification, apply the function
		//specified by the first argument of Map
		if level >= spec.min {
			newExpression = f(
				head,
				newExpression,
				currentPartSpec,
				generated,
				es,
			)
			toReturn.AppendEx(newExpression)
		} else {
			toReturn.AppendEx(newExpression)
		}
	}

	return toReturn
}

func expressionWalkMapBackwards(
	f func(expreduceapi.Ex, expreduceapi.Ex, []int64, *int64, expreduceapi.EvalStateInterface) expreduceapi.Ex,
	head expreduceapi.Ex,
	partSpec []int64,
	this expreduceapi.ExpressionInterface,
	es expreduceapi.EvalStateInterface,
	spec levelSpec,
	generated *int64,
) (expreduceapi.ExpressionInterface, int64) {
	toReturn := atoms.NewExpression([]expreduceapi.Ex{this.GetParts()[0]})
	currentMaxDepth := int64(1)

	for i, expr := range this.GetParts()[1:] {
		newExpression := expr
		var depth int64

		currentPartSpec := append(partSpec, int64(i+1))
		level := int64(len(currentPartSpec))

		expression, isExpression := newExpression.(expreduceapi.ExpressionInterface)
		if isExpression {
			//Determine the depth of this part
			newExpression, depth = expressionWalkMapBackwards(
				f,
				head,
				currentPartSpec,
				expression,
				es,
				spec,
				generated,
			)
			if depth > currentMaxDepth {
				currentMaxDepth = depth
			}

			if spec.checkLevel(level) && spec.checkDepth(depth) {
				newExpression = f(
					head,
					newExpression,
					currentPartSpec,
					generated,
					es,
				)
				toReturn.AppendEx(newExpression)
			} else {
				toReturn.AppendEx(newExpression)
			}
		} else { //If the node is atomic
			level = level + 1
			depth = int64(1)

			if spec.checkLevel(level) && spec.checkDepth(depth) {
				newExpression = f(head, expr, currentPartSpec, generated, es)
				toReturn.AppendEx(newExpression)
			} else {
				toReturn.AppendEx(newExpression)
			}
		}
	}

	return toReturn, currentMaxDepth + 1
}

func wrapWithHead(
	head expreduceapi.Ex,
	expr expreduceapi.Ex,
	partList []int64,
	_ *int64,
	es expreduceapi.EvalStateInterface,
) expreduceapi.Ex {
	return atoms.NewExpression([]expreduceapi.Ex{head, expr})
}

func wrapWithHeadIndexed(
	head expreduceapi.Ex,
	expr expreduceapi.Ex,
	partList []int64,
	_ *int64,
	es expreduceapi.EvalStateInterface,
) expreduceapi.Ex {
	partSpec := []expreduceapi.Ex{atoms.NewSymbol("System`List")}
	for _, part := range partList {
		partSpec = append(partSpec, atoms.NewInt(part))
	}
	partSpecExpr := atoms.NewExpression(partSpec)
	return atoms.NewExpression([]expreduceapi.Ex{head, expr, partSpecExpr})
}

func applyHead(
	head expreduceapi.Ex,
	expr expreduceapi.Ex,
	partList []int64,
	_ *int64,
	es expreduceapi.EvalStateInterface,
) expreduceapi.Ex {
	expression, isExpr := expr.(expreduceapi.ExpressionInterface)
	if !isExpr {
		return expr
	}
	toReturn := atoms.NewExpression([]expreduceapi.Ex{head})
	//toReturn.AppendExArray(expression.GetParts()[1:])
	toReturn.AppendExArray(expression.GetParts()[1:])
	return toReturn
}

type levelSpecOptimizationStrategy int

const (
	unoptimizedSimpleLevelSpec levelSpecOptimizationStrategy = iota
	mapOptimizedSimpleLevelSpec
	applyOptimizedSimpleLevelSpec
)

func exOrGenerated(
	e expreduceapi.Ex,
	generated *int64,
	returnGenerated bool,
) expreduceapi.Ex {
	if returnGenerated {
		return atoms.NewInt(*generated)
	}
	return e
}

func levelSpecFunction(
	f func(expreduceapi.Ex, expreduceapi.Ex, []int64, *int64, expreduceapi.EvalStateInterface) expreduceapi.Ex,
	optStrat levelSpecOptimizationStrategy,
	returnGenerated bool,
	leveledExprIsFirst bool,
) func(expreduceapi.ExpressionInterface, expreduceapi.EvalStateInterface) expreduceapi.Ex {
	return func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
		// Optimization of the very common case where the levelspec-ed
		// operation has two arguments
		if len(this.GetParts()) == 3 {
			if optStrat == mapOptimizedSimpleLevelSpec {
				expr, isExpr := this.GetParts()[2].(expreduceapi.ExpressionInterface)
				if isExpr {
					toReturn := atoms.NewExpression(
						[]expreduceapi.Ex{expr.GetParts()[0]},
					)
					for i := 1; i < len(expr.GetParts()); i++ {
						toReturn.AppendEx(atoms.NewExpression([]expreduceapi.Ex{
							this.GetParts()[1],
							expr.GetParts()[i],
						}))
					}
					return toReturn
				}
				return this.GetParts()[2]
			} else if optStrat == applyOptimizedSimpleLevelSpec {
				sym, isSym := this.GetParts()[1].(*atoms.Symbol)
				expr, isExpr := this.GetParts()[2].(expreduceapi.ExpressionInterface)
				if isSym && isExpr {
					toReturn := atoms.NewExpression([]expreduceapi.Ex{sym})
					toReturn.AppendExArray(expr.GetParts()[1:])
					return es.Eval(toReturn)
				}
				return this.GetParts()[2]
			}
		}

		if len(this.GetParts()) != 4 {
			return this
		}

		spec := parseLevelSpec(this.GetParts()[3], es)
		if !spec.isValid() {
			return this
		}

		// For example the function to apply for Map or the pattern to match
		// for Count.
		dataExpr := this.GetParts()[1]
		leveledExpr := this.GetParts()[2]
		if leveledExprIsFirst {
			dataExpr = this.GetParts()[2]
			leveledExpr = this.GetParts()[1]
		}
		generatedData := int64(0)
		generated := &generatedData

		// If the leveled expression is atomic, it will be ignored except in
		// one case
		expression, nonAtomic := leveledExpr.(expreduceapi.ExpressionInterface)
		if !nonAtomic {
			if spec.checkLevel(0) && spec.checkDepth(0) {
				return exOrGenerated(
					f(dataExpr, leveledExpr, []int64{}, generated, es),
					generated,
					returnGenerated,
				)
			}
			return exOrGenerated(leveledExpr, generated, returnGenerated)
		}

		if spec.min == 0 && spec.max == 0 {
			return exOrGenerated(
				f(dataExpr, leveledExpr, []int64{}, generated, es),
				generated,
				returnGenerated,
			)
		}

		//In this special case we do not have to keep track of depth, this can be computed faster
		//than when depth is required because we do not always have to recurse all the way to the
		//bottom of the expression
		if !spec.isMinDepth && !spec.isMaxDepth {
			newExpression := expressionWalkMap(
				f,
				dataExpr,
				[]int64{},
				expression,
				es,
				spec,
				generated,
			)

			if spec.checkLevel(0) && spec.checkDepth(0) {
				return exOrGenerated(
					f(dataExpr, newExpression, []int64{}, generated, es),
					generated,
					returnGenerated,
				)
			}
			return exOrGenerated(newExpression, generated, returnGenerated)
		}

		//We now turn to the most general case, where levels can be specified as either
		//positive or negative integers, where negative integers denote depth rather than level
		newExpression, depth := expressionWalkMapBackwards(
			f,
			dataExpr,
			[]int64{},
			expression,
			es,
			spec,
			generated,
		)

		//Whether to wrap the zeroth level with the function.
		if spec.checkLevel(0) && spec.checkDepth(depth) {
			return exOrGenerated(
				f(dataExpr, newExpression, []int64{}, generated, es),
				generated,
				returnGenerated,
			)
		}
		return exOrGenerated(newExpression, generated, returnGenerated)
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
		legacyEvalFn: levelSpecFunction(
			applyHead,
			applyOptimizedSimpleLevelSpec,
			false,
			false,
		),
	})
	defs = append(defs, Definition{
		Name: "Map",
		legacyEvalFn: levelSpecFunction(
			wrapWithHead,
			mapOptimizedSimpleLevelSpec,
			false,
			false,
		),
	})

	defs = append(defs, Definition{
		Name: "MapIndexed",
		legacyEvalFn: levelSpecFunction(
			wrapWithHeadIndexed,
			mapOptimizedSimpleLevelSpec,
			false,
			false,
		),
	})

	defs = append(defs, Definition{
		Name: "FoldList",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 4 {
				return this
			}

			f := this.GetParts()[1]
			first := this.GetParts()[2]
			values, nonAtomic := this.GetParts()[3].(expreduceapi.ExpressionInterface)

			if !nonAtomic {
				return this
			}

			toReturn := atoms.NewExpression(
				[]expreduceapi.Ex{values.GetParts()[0], first},
			)

			if len(values.GetParts()) < 2 {
				return toReturn
			}

			expr := atoms.NewExpression([]expreduceapi.Ex{
				f,
				first,
				values.GetParts()[1],
			})

			toReturn.AppendEx(expr)

			for i := 2; i < len(values.GetParts()); i++ {
				expr = atoms.NewExpression([]expreduceapi.Ex{
					f,
					expr,
					values.GetParts()[i],
				})

				toReturn.AppendEx(expr)
			}

			return toReturn
		},
	})
	defs = append(defs, Definition{Name: "Fold"})

	defs = append(defs, Definition{
		Name: "NestList",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 4 {
				return this
			}

			f := this.GetParts()[1]
			expr := this.GetParts()[2]
			nInt, isInteger := this.GetParts()[3].(*atoms.Integer)
			if !isInteger {
				return this
			}
			n := nInt.Val.Int64()
			if n < 0 {
				return this
			}

			toReturn := atoms.NewExpression(
				[]expreduceapi.Ex{atoms.NewSymbol("System`List"), expr},
			)

			for i := int64(1); i <= n; i++ {
				expr = atoms.NewExpression([]expreduceapi.Ex{
					f,
					expr,
				})

				toReturn.AppendEx(expr)
			}

			return toReturn
		},
	})

	defs = append(defs, Definition{Name: "Nest"})
	defs = append(defs, Definition{
		Name: "NestWhileList",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) < 4 || len(this.GetParts()) > 7 {
				return this
			}

			f := this.GetParts()[1]
			expr := this.GetParts()[2]
			test := this.GetParts()[3]

			m := int64(1)
			if len(this.GetParts()) > 4 {
				mInt, isInteger := this.GetParts()[4].(*atoms.Integer)
				mSymbol, isSymbol := this.GetParts()[4].(*atoms.Symbol)
				if isInteger {
					m = mInt.Val.Int64()
					if m < 0 {
						return this
					}
				} else if isSymbol {
					if mSymbol.IsEqual(atoms.NewSymbol("System`All")) == "EQUAL_TRUE" {
						m = -1
					} else {
						return this
					}
				} else {
					return this
				}
			}

			max := int64(-1)
			if len(this.GetParts()) > 5 {
				maxInt, isInteger := this.GetParts()[5].(*atoms.Integer)
				maxSymbol, isSymbol := this.GetParts()[5].(*atoms.Symbol)
				if isInteger {
					max = maxInt.Val.Int64()
					if maxInt.Val.Int64() < 0 {
						return this
					}
				} else if isSymbol {
					if maxSymbol.IsEqual(atoms.NewSymbol("System`Infinity")) == "EQUAL_TRUE" {
						max = -1
					} else {
						return this
					}
				} else {
					return this
				}
			}

			n := int64(0)
			if len(this.GetParts()) > 6 {
				bonusIterationsInt, isInteger := this.GetParts()[6].(*atoms.Integer)
				if isInteger && bonusIterationsInt.Val.Int64() >= int64(0) {
					n = bonusIterationsInt.Val.Int64()
				}
			}

			evaluated := []expreduceapi.Ex{es.Eval(expr.DeepCopy())}
			toReturn := atoms.NewExpression(
				[]expreduceapi.Ex{atoms.NewSymbol("System`List"), expr},
			)

			isequal := "EQUAL_TRUE"
			cont := isequal == "EQUAL_TRUE"
			for i := int64(2); cont; i++ {
				expr = atoms.NewExpression([]expreduceapi.Ex{
					f,
					expr,
				})

				toReturn.AppendEx(expr)
				evaluated = append(
					evaluated,
					es.Eval(expr.DeepCopy()),
				) // Could use a stack of length m

				if i >= m {
					testExpression := atoms.NewExpression(
						[]expreduceapi.Ex{test},
					)
					if m >= 0 {
						testExpression.AppendExArray(
							evaluated[int64(len(evaluated))-m:],
						)
					} else {
						testExpression.AppendExArray(evaluated)
					}
					isequal = es.Eval(testExpression).
						IsEqual(atoms.NewSymbol("System`True"))
					cont = isequal == "EQUAL_TRUE"
				}

				if i > max && max != -1 {
					cont = false
				}
			}

			if n > 0 {
				for i := int64(0); i < n; i++ {
					expr = atoms.NewExpression([]expreduceapi.Ex{
						f,
						expr,
					})

					toReturn.AppendEx(expr)
				}
			} else {
				toReturn.SetParts(toReturn.GetParts()[:int64(len(toReturn.GetParts()))+n])
			}

			return toReturn
		},
	})
	defs = append(defs, Definition{Name: "NestWhile"})
	defs = append(defs, Definition{Name: "FixedPointList"})
	defs = append(defs, Definition{
		Name: "FixedPoint",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 3 {
				return this
			}

			currVal := this.GetParts()[2]
			nextVal := es.Eval(atoms.E(this.GetParts()[1], currVal))
			for !atoms.IsSameQ(currVal, nextVal) {
				currVal = nextVal
				nextVal = es.Eval(atoms.E(this.GetParts()[1], currVal))
			}
			return nextVal
		},
	})
	defs = append(defs, Definition{
		Name: "Array",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 3 {
				return this
			}

			nInt, nOk := this.GetParts()[2].(*atoms.Integer)
			if nOk {
				n := nInt.Val.Int64()
				toReturn := atoms.NewExpression(
					[]expreduceapi.Ex{atoms.NewSymbol("System`List")},
				)
				for i := int64(1); i <= n; i++ {
					toReturn.AppendEx(atoms.NewExpression([]expreduceapi.Ex{
						this.GetParts()[1],
						atoms.NewInteger(big.NewInt(i)),
					}))
				}
				return toReturn
			}
			return this.GetParts()[2]
		},
	})
	defs = append(defs, Definition{
		Name: "Identity",
	})
	return
}
