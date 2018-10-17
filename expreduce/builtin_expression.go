package expreduce

import (
	"math/big"

	"github.com/corywalker/expreduce/expreduce/logging"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

func CalcDepth(ex expreduceapi.Ex) int {
	expr, isExpr := ex.(expreduceapi.ExpressionInterface)
	if !isExpr {
		return 1
	}
	theMax := 1
	// Find max depth of params. Heads are not counted.
	for i := 1; i < len(expr.Parts); i++ {
		theMax = Max(theMax, CalcDepth(expr.Parts[i]))
	}
	return theMax + 1
}

func flattenExpr(src expreduceapi.ExpressionInterface, dst expreduceapi.ExpressionInterface, level int64, cl *logging.CASLogger) {
	continueFlatten := level > 0
	for i := 1; i < len(src.Parts); i++ {
		expr, isExpr := src.Parts[i].(expreduceapi.ExpressionInterface)
		if continueFlatten && isExpr {
			if IsSameQ(src.Parts[0], expr.Parts[0], cl) {
				flattenExpr(expr, dst, level-1, cl)
				continue
			}
		}
		dst.Parts = append(dst.Parts, src.Parts[i])
	}
}

func leafCount(e expreduceapi.Ex) int64 {
	if asExpr, isExpr := e.(expreduceapi.ExpressionInterface); isExpr {
		res := int64(0)
		for _, part := range asExpr.Parts {
			res += leafCount(part)
		}
		return res
	}
	return 1
}

func GetExpressionDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "Head",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.Parts) != 2 {
				return this
			}

			_, IsFlt := this.Parts[1].(*Flt)
			if IsFlt {
				return NewSymbol("System`Real")
			}
			_, IsInteger := this.Parts[1].(*Integer)
			if IsInteger {
				return NewSymbol("System`Integer")
			}
			_, IsString := this.Parts[1].(*String)
			if IsString {
				return NewSymbol("System`String")
			}
			_, IsSymbol := this.Parts[1].(*Symbol)
			if IsSymbol {
				return NewSymbol("System`Symbol")
			}
			_, IsRational := this.Parts[1].(*Rational)
			if IsRational {
				return NewSymbol("System`Rational")
			}
			_, IsComplex := this.Parts[1].(*Complex)
			if IsComplex {
				return NewSymbol("System`Complex")
			}
			asExpr, IsExpression := this.Parts[1].(expreduceapi.ExpressionInterface)
			if IsExpression {
				return asExpr.Parts[0]
			}
			return this
		},
	})
	defs = append(defs, Definition{
		Name: "Depth",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.Parts) != 2 {
				return this
			}
			return NewInteger(big.NewInt(int64(CalcDepth(this.Parts[1]))))
		},
	})
	defs = append(defs, Definition{
		Name: "Length",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.Parts) != 2 {
				return this
			}

			expr, isExpr := this.Parts[1].(expreduceapi.ExpressionInterface)
			if isExpr {
				return NewInteger(big.NewInt(int64(len(expr.Parts) - 1)))
			}
			return NewInteger(big.NewInt(0))
		},
	})
	defs = append(defs, Definition{
		Name: "Sequence",
	})
	defs = append(defs, Definition{
		Name: "Evaluate",
	})
	defs = append(defs, Definition{
		Name: "Hold",
	})
	defs = append(defs, Definition{
		Name: "HoldForm",
		toString: func(this expreduceapi.ExpressionInterface, params expreduceapi.ToStringParams) (bool, string) {
			if len(this.Parts) != 2 {
				return false, ""
			}
			if params.form == "FullForm" {
				return false, ""
			}
			return true, this.Parts[1].StringForm(params)
		},
	})
	defs = append(defs, Definition{
		Name: "Flatten",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.Parts) < 2 {
				return this
			}
			level := int64(999999999999)
			if len(this.Parts) > 2 {
				asInt, isInt := this.Parts[2].(*Integer)
				if !isInt {
					return this
				}
				level = int64(asInt.Val.Int64())
			}
			expr, isExpr := this.Parts[1].(expreduceapi.ExpressionInterface)
			if !isExpr {
				return this
			}
			dst := NewExpression([]expreduceapi.Ex{expr.Parts[0]})
			flattenExpr(expr, dst, level, &es.CASLogger)
			return dst
		},
	})
	defs = append(defs, Definition{
		Name: "LeafCount",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.Parts) != 2 {
				return this
			}
			return NewInt(leafCount(this.Parts[1]))
		},
	})
	defs = append(defs, Definition{
		Name:              "Flat",
		OmitDocumentation: true,
	})
	defs = append(defs, Definition{
		Name:              "Orderless",
		OmitDocumentation: true,
	})
	defs = append(defs, Definition{
		Name:              "OneIdentity",
		OmitDocumentation: true,
	})
	defs = append(defs, Definition{Name: "Unevaluated"})
	defs = append(defs, Definition{Name: "HoldComplete"})
	return
}
