package expreduce

import (
	"sort"

	"github.com/corywalker/expreduce/expreduce/atoms"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

type extremaFnType int

const (
	maxFn extremaFnType = iota
	minFn
)

func extremaFunction(
	this expreduceapi.ExpressionInterface,
	fnType extremaFnType,
	es expreduceapi.EvalStateInterface,
) expreduceapi.Ex {
	// Flatten nested lists into arguments.
	origHead := this.GetParts()[0]
	this.GetParts()[0] = atoms.S("List")
	dst := atoms.E(atoms.S("List"))
	flattenExpr(this, dst, 999999999, es.GetLogger())
	// Previously I always set the pointer but it led to an endless
	// eval loop. I think evaluation might use the pointer to make a
	// "same" comparison.
	if !atoms.IsSameQ(this, dst) {
		this = dst
		sort.Sort(this)
	}
	this.GetParts()[0] = origHead

	if len(this.GetParts()) == 1 {
		if fnType == maxFn {
			return atoms.E(
				atoms.S("Times"),
				atoms.NewInt(-1),
				atoms.S("Infinity"),
			)
		}
		return atoms.S("Infinity")
	}
	if len(this.GetParts()) == 2 {
		return this.GetParts()[1]
	}
	var i int
	for i = 1; i < len(this.GetParts()); i++ {
		if !atoms.NumberQ(this.GetParts()[i]) {
			break
		}
	}
	if fnType == maxFn {
		i--
		return atoms.NewExpression(
			append(
				[]expreduceapi.Ex{this.GetParts()[0]},
				this.GetParts()[i:]...),
		)
	}
	if i == 1 {
		return this
	}
	return atoms.NewExpression(
		append(this.GetParts()[:2], this.GetParts()[i:]...),
	)
}

func getCompSign(e expreduceapi.Ex) int {
	sym, isSym := e.(*atoms.Symbol)
	if !isSym {
		return -2
	}
	switch sym.Name {
	case "System`Less":
		return -1
	case "System`LessEqual":
		return -1
	case "System`Equal":
		return 0
	case "System`GreaterEqual":
		return 1
	case "System`Greater":
		return 1
	}
	return -2
}

func getComparisonDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "Equal",
		toString: func(this expreduceapi.ExpressionInterface, params expreduceapi.ToStringParams) (bool, string) {
			return toStringInfixAdvanced(
				this.GetParts()[1:],
				" == ",
				"System`Equal",
				false,
				"",
				"",
				params,
			)
		},
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) < 1 {
				return this
			}

			isequal := true
			for i := 2; i < len(this.GetParts()); i++ {
				var equalstr string = this.GetParts()[1].IsEqual(this.GetParts()[i])
				if equalstr == "EQUAL_UNK" {
					return this
				}
				isequal = isequal && (equalstr == "EQUAL_TRUE")
			}
			if isequal {
				return atoms.NewSymbol("System`True")
			}
			return atoms.NewSymbol("System`False")
		},
	})
	defs = append(defs, Definition{
		Name: "Unequal",
		toString: func(this expreduceapi.ExpressionInterface, params expreduceapi.ToStringParams) (bool, string) {
			return toStringInfixAdvanced(
				this.GetParts()[1:],
				" != ",
				"System`Unequal",
				false,
				"",
				"",
				params,
			)
		},
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 3 {
				return this
			}

			var isequal string = this.GetParts()[1].IsEqual(this.GetParts()[2])
			if isequal == "EQUAL_UNK" {
				return this
			} else if isequal == "EQUAL_TRUE" {
				return atoms.NewSymbol("System`False")
			} else if isequal == "EQUAL_FALSE" {
				return atoms.NewSymbol("System`True")
			}

			return atoms.NewExpression(
				[]expreduceapi.Ex{
					atoms.NewSymbol("System`Error"),
					atoms.NewString("Unexpected equality return value."),
				},
			)
		},
	})
	defs = append(defs, Definition{
		Name: "SameQ",
		toString: func(this expreduceapi.ExpressionInterface, params expreduceapi.ToStringParams) (bool, string) {
			return toStringInfixAdvanced(
				this.GetParts()[1:],
				" === ",
				"System`SameQ",
				false,
				"",
				"",
				params,
			)
		},
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) < 1 {
				return this
			}

			issame := true
			for i := 2; i < len(this.GetParts()); i++ {
				issame = issame &&
					atoms.IsSameQ(this.GetParts()[1], this.GetParts()[i])
			}
			if issame {
				return atoms.NewSymbol("System`True")
			}
			return atoms.NewSymbol("System`False")
		},
	})
	defs = append(defs, Definition{
		Name: "UnsameQ",
		toString: func(this expreduceapi.ExpressionInterface, params expreduceapi.ToStringParams) (bool, string) {
			return toStringInfixAdvanced(
				this.GetParts()[1:],
				" =!= ",
				"System`UnsameQ",
				false,
				"",
				"",
				params,
			)
		},
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) < 1 {
				return this
			}

			for i := 1; i < len(this.GetParts()); i++ {
				for j := i + 1; j < len(this.GetParts()); j++ {
					if atoms.IsSameQ(this.GetParts()[i], this.GetParts()[j]) {
						return atoms.NewSymbol("System`False")
					}
				}
			}
			return atoms.NewSymbol("System`True")
		},
	})
	defs = append(defs, Definition{
		Name: "AtomQ",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 2 {
				return this
			}

			_, isExpr := this.GetParts()[1].(expreduceapi.ExpressionInterface)
			if isExpr {
				return atoms.NewSymbol("System`False")
			}
			return atoms.NewSymbol("System`True")
		},
	})
	defs = append(defs, Definition{
		Name:         "NumberQ",
		legacyEvalFn: singleParamQEval(atoms.NumberQ),
	})
	defs = append(defs, Definition{
		Name: "NumericQ",
	})
	defs = append(defs, Definition{
		Name: "Less",
		toString: func(this expreduceapi.ExpressionInterface, params expreduceapi.ToStringParams) (bool, string) {
			return toStringInfixAdvanced(
				this.GetParts()[1:],
				" < ",
				"",
				true,
				"",
				"",
				params,
			)
		},
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 3 {
				return this
			}

			a := es.Eval(
				atoms.NewExpression(
					[]expreduceapi.Ex{
						atoms.NewSymbol("System`N"),
						this.GetParts()[1],
					},
				),
			)
			b := es.Eval(
				atoms.NewExpression(
					[]expreduceapi.Ex{
						atoms.NewSymbol("System`N"),
						this.GetParts()[2],
					},
				),
			)

			if !atoms.NumberQ(a) || !atoms.NumberQ(b) {
				return this
			}

			// Less
			if atoms.ExOrder(a, b) == 1 {
				return atoms.NewSymbol("System`True")
			}
			return atoms.NewSymbol("System`False")
		},
	})
	defs = append(defs, Definition{
		Name: "Greater",
		toString: func(this expreduceapi.ExpressionInterface, params expreduceapi.ToStringParams) (bool, string) {
			return toStringInfixAdvanced(
				this.GetParts()[1:],
				" > ",
				"",
				true,
				"",
				"",
				params,
			)
		},
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 3 {
				return this
			}

			a := es.Eval(
				atoms.NewExpression(
					[]expreduceapi.Ex{
						atoms.NewSymbol("System`N"),
						this.GetParts()[1],
					},
				),
			)
			b := es.Eval(
				atoms.NewExpression(
					[]expreduceapi.Ex{
						atoms.NewSymbol("System`N"),
						this.GetParts()[2],
					},
				),
			)

			if !atoms.NumberQ(a) || !atoms.NumberQ(b) {
				return this
			}
			// Greater
			if atoms.ExOrder(a, b) == -1 {
				return atoms.NewSymbol("System`True")
			}
			return atoms.NewSymbol("System`False")
		},
	})
	defs = append(defs, Definition{
		Name: "LessEqual",
		toString: func(this expreduceapi.ExpressionInterface, params expreduceapi.ToStringParams) (bool, string) {
			return toStringInfixAdvanced(
				this.GetParts()[1:],
				" <= ",
				"",
				true,
				"",
				"",
				params,
			)
		},
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 3 {
				return this
			}

			a := es.Eval(
				atoms.NewExpression(
					[]expreduceapi.Ex{
						atoms.NewSymbol("System`N"),
						this.GetParts()[1],
					},
				),
			)
			b := es.Eval(
				atoms.NewExpression(
					[]expreduceapi.Ex{
						atoms.NewSymbol("System`N"),
						this.GetParts()[2],
					},
				),
			)

			if !atoms.NumberQ(a) || !atoms.NumberQ(b) {
				return this
			}
			// Less
			if atoms.ExOrder(a, b) == 1 {
				return atoms.NewSymbol("System`True")
			}
			// Equal
			if atoms.ExOrder(a, b) == 0 {
				return atoms.NewSymbol("System`True")
			}
			return atoms.NewSymbol("System`False")
		},
	})
	defs = append(defs, Definition{
		Name: "GreaterEqual",
		toString: func(this expreduceapi.ExpressionInterface, params expreduceapi.ToStringParams) (bool, string) {
			return toStringInfixAdvanced(
				this.GetParts()[1:],
				" >= ",
				"",
				true,
				"",
				"",
				params,
			)
		},
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 3 {
				return this
			}

			a := es.Eval(
				atoms.NewExpression(
					[]expreduceapi.Ex{
						atoms.NewSymbol("System`N"),
						this.GetParts()[1],
					},
				),
			)
			b := es.Eval(
				atoms.NewExpression(
					[]expreduceapi.Ex{
						atoms.NewSymbol("System`N"),
						this.GetParts()[2],
					},
				),
			)

			if !atoms.NumberQ(a) || !atoms.NumberQ(b) {
				return this
			}
			// Greater
			if atoms.ExOrder(a, b) == -1 {
				return atoms.NewSymbol("System`True")
			}
			// Equal
			if atoms.ExOrder(a, b) == 0 {
				return atoms.NewSymbol("System`True")
			}
			return atoms.NewSymbol("System`False")
		},
	})
	defs = append(defs, Definition{
		Name: "Positive",
	})
	defs = append(defs, Definition{
		Name: "Negative",
	})
	defs = append(defs, Definition{
		Name: "Max",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			return extremaFunction(this, maxFn, es)
		},
	})
	defs = append(defs, Definition{
		Name: "Min",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			return extremaFunction(this, minFn, es)
		},
	})
	defs = append(defs, Definition{Name: "PossibleZeroQ"})
	defs = append(defs, Definition{Name: "MinMax"})
	defs = append(defs, Definition{Name: "Element"})
	defs = append(defs, Definition{
		Name: "Inequality",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) == 1 {
				return this
			}
			if len(this.GetParts()) == 2 {
				return atoms.S("True")
			}
			if len(this.GetParts())%2 != 0 {
				return this
			}
			firstSign := getCompSign(this.GetParts()[2])
			if firstSign == -2 {
				return this
			}
			if firstSign != 0 {
				for i := 4; i < len(this.GetParts()); i += 2 {
					thisSign := getCompSign(this.GetParts()[i])
					if thisSign == -2 {
						return this
					}
					if thisSign == -firstSign {
						firstIneq := atoms.E(atoms.S("Inequality"))
						secondIneq := atoms.E(atoms.S("Inequality"))
						for j := 1; j < len(this.GetParts()); j++ {
							if j < i {
								firstIneq.AppendEx(this.GetParts()[j])
							}
							if j > (i - 2) {
								secondIneq.AppendEx(this.GetParts()[j])
							}
						}
						return atoms.E(atoms.S("And"), firstIneq, secondIneq)
					}
				}
			}
			res := atoms.E(atoms.S("Inequality"))
			for i := 0; i < (len(this.GetParts())-1)/2; i++ {
				lhs := this.GetParts()[2*i+1]
				if len(res.GetParts()) > 1 {
					lhs = res.GetParts()[len(res.GetParts())-1]
				}
				op := this.GetParts()[2*i+2]
				rhs := this.GetParts()[2*i+3]
				for rhsI := 2*i + 3; rhsI < len(this.GetParts()); rhsI += 2 {
					if falseQ(
						es.Eval(atoms.E(op, lhs, this.GetParts()[rhsI])),
						es.GetLogger(),
					) {
						return atoms.S("False")
					}
				}
				evalRes := es.Eval(atoms.E(op, lhs, rhs))
				if !trueQ(evalRes, es.GetLogger()) {
					if !atoms.IsSameQ(
						res.GetParts()[len(res.GetParts())-1],
						lhs,
					) {
						res.AppendEx(lhs)
					}
					res.AppendEx(op)
					res.AppendEx(rhs)
				}
			}
			if len(res.GetParts()) == 1 {
				return atoms.S("True")
			}
			if len(res.GetParts()) == 4 {
				return atoms.E(
					res.GetParts()[2],
					res.GetParts()[1],
					res.GetParts()[3],
				)
			}
			return res
		},
	})
	return
}
