package expreduce

import (
	"math/big"

	"github.com/corywalker/expreduce/expreduce/atoms"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

type singleParamQType (func(expreduceapi.Ex) bool)

type singleParamQLogType (func(expreduceapi.Ex, expreduceapi.LoggingInterface) bool)

type evalFnType (func(expreduceapi.ExpressionInterface, expreduceapi.EvalStateInterface) expreduceapi.Ex)

func singleParamQEval(fn singleParamQType) evalFnType {
	return (func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
		if len(this.GetParts()) != 2 {
			return this
		}
		if fn(this.GetParts()[1]) {
			return atoms.NewSymbol("System`True")
		}
		return atoms.NewSymbol("System`False")
	})
}

func singleParamQLogEval(fn singleParamQLogType) evalFnType {
	return (func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
		if len(this.GetParts()) != 2 {
			return this
		}
		if fn(this.GetParts()[1], es.GetLogger()) {
			return atoms.NewSymbol("System`True")
		}
		return atoms.NewSymbol("System`False")
	})
}

func vectorQ(e expreduceapi.Ex) bool {
	l, isL := atoms.HeadAssertion(e, "System`List")
	if isL {
		for i := 1; i < len(l.GetParts()); i++ {
			_, subIsL := atoms.HeadAssertion(l.GetParts()[i], "System`List")
			if subIsL {
				return false
			}
		}
		return true
	}
	return false
}

func matrixQ(e expreduceapi.Ex, cl expreduceapi.LoggingInterface) bool {
	l, isL := atoms.HeadAssertion(e, "System`List")
	if isL {
		return len(dimensions(l, 0, cl)) == 2
	}
	return false
}

func symbolNameQ(
	e expreduceapi.Ex,
	name string,
	cl expreduceapi.LoggingInterface,
) bool {
	sym, isSym := e.(*atoms.Symbol)
	if isSym {
		return sym.Name == name
	}
	return false
}

func trueQ(e expreduceapi.Ex, cl expreduceapi.LoggingInterface) bool {
	return symbolNameQ(e, "System`True", cl)
}

func falseQ(e expreduceapi.Ex, cl expreduceapi.LoggingInterface) bool {
	return symbolNameQ(e, "System`False", cl)
}

func booleanQ(e expreduceapi.Ex, cl expreduceapi.LoggingInterface) bool {
	sym, isSym := e.(*atoms.Symbol)
	if isSym {
		return sym.Name == "System`False" || sym.Name == "System`True"
	}
	return false
}

func primeQ(e expreduceapi.Ex) bool {
	asInt, ok := e.(*atoms.Integer)
	if !ok {
		return false
	}
	abs := big.NewInt(0)
	abs.Abs(asInt.Val)
	return abs.ProbablyPrime(16)
}
