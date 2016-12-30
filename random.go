package cas

import "math/big"
import "math/rand"

func (this *Expression) EvalRandomReal(es *EvalState) Ex {
	if len(this.Parts) != 1 {
		return this
	}

	return &Flt{big.NewFloat(rand.Float64())}
}

func (this *Expression) EvalSeedRandom(es *EvalState) Ex {
	if len(this.Parts) != 2 {
		return this
	}

	asInt, isInt := this.Parts[1].(*Integer)
	if isInt {
		rand.Seed(asInt.Val.Int64())
		return &Symbol{"Null"}
	}

	return this
}

func GetRandomDefinitions() (defs []Definition) {
	return
}
