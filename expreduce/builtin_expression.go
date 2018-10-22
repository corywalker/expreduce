package expreduce

import (
	"math/big"

	"github.com/corywalker/expreduce/expreduce/atoms"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

func CalcDepth(ex expreduceapi.Ex) int {
	expr, isExpr := ex.(expreduceapi.ExpressionInterface)
	if !isExpr {
		return 1
	}
	theMax := 1
	// Find max depth of params. Heads are not counted.
	for i := 1; i < len(expr.GetParts()); i++ {
		theMax = Max(theMax, CalcDepth(expr.GetParts()[i]))
	}
	return theMax + 1
}

func flattenExpr(src expreduceapi.ExpressionInterface, dst expreduceapi.ExpressionInterface, level int64, cl expreduceapi.LoggingInterface) {
	continueFlatten := level > 0
	for i := 1; i < len(src.GetParts()); i++ {
		expr, isExpr := src.GetParts()[i].(expreduceapi.ExpressionInterface)
		if continueFlatten && isExpr {
			if atoms.IsSameQ(src.GetParts()[0], expr.GetParts()[0], cl) {
				flattenExpr(expr, dst, level-1, cl)
				continue
			}
		}
		dst.AppendEx(src.GetParts()[i])
	}
}

func leafCount(e expreduceapi.Ex) int64 {
	if asExpr, isExpr := e.(expreduceapi.ExpressionInterface); isExpr {
		res := int64(0)
		for _, part := range asExpr.GetParts() {
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
			if len(this.GetParts()) != 2 {
				return this
			}

			_, IsFlt := this.GetParts()[1].(*atoms.Flt)
			if IsFlt {
				return atoms.NewSymbol("System`Real")
			}
			_, IsInteger := this.GetParts()[1].(*atoms.Integer)
			if IsInteger {
				return atoms.NewSymbol("System`Integer")
			}
			_, IsString := this.GetParts()[1].(*atoms.String)
			if IsString {
				return atoms.NewSymbol("System`String")
			}
			_, IsSymbol := this.GetParts()[1].(*atoms.Symbol)
			if IsSymbol {
				return atoms.NewSymbol("System`Symbol")
			}
			_, IsRational := this.GetParts()[1].(*atoms.Rational)
			if IsRational {
				return atoms.NewSymbol("System`Rational")
			}
			_, IsComplex := this.GetParts()[1].(*atoms.Complex)
			if IsComplex {
				return atoms.NewSymbol("System`Complex")
			}
			asExpr, IsExpression := this.GetParts()[1].(expreduceapi.ExpressionInterface)
			if IsExpression {
				return asExpr.GetParts()[0]
			}
			return this
		},
	})
	defs = append(defs, Definition{
		Name: "Depth",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 2 {
				return this
			}
			return atoms.NewInteger(big.NewInt(int64(CalcDepth(this.GetParts()[1]))))
		},
	})
	defs = append(defs, Definition{
		Name: "Length",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 2 {
				return this
			}

			expr, isExpr := this.GetParts()[1].(expreduceapi.ExpressionInterface)
			if isExpr {
				return atoms.NewInteger(big.NewInt(int64(len(expr.GetParts()) - 1)))
			}
			return atoms.NewInteger(big.NewInt(0))
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
			if len(this.GetParts()) != 2 {
				return false, ""
			}
			if params.Form == "FullForm" {
				return false, ""
			}
			return true, this.GetParts()[1].StringForm(params)
		},
	})
	defs = append(defs, Definition{
		Name: "Flatten",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) < 2 {
				return this
			}
			level := int64(999999999999)
			if len(this.GetParts()) > 2 {
				asInt, isInt := this.GetParts()[2].(*atoms.Integer)
				if !isInt {
					return this
				}
				level = int64(asInt.Val.Int64())
			}
			expr, isExpr := this.GetParts()[1].(expreduceapi.ExpressionInterface)
			if !isExpr {
				return this
			}
			dst := atoms.NewExpression([]expreduceapi.Ex{expr.GetParts()[0]})
			flattenExpr(expr, dst, level, es.GetLogger())
			return dst
		},
	})
	defs = append(defs, Definition{
		Name: "LeafCount",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 2 {
				return this
			}
			return atoms.NewInt(leafCount(this.GetParts()[1]))
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
