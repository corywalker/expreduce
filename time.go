package cas

import "math/big"
import "time"

func (this *Expression) EvalUnixTime(es *EvalState) Ex {
	if len(this.Parts) != 1 {
		return this
	}

	return &Integer{big.NewInt(time.Now().UTC().Unix())}
}

func GetTimeDefinitions() (defs []Definition) {
	return
}
