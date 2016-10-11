package cas

import "bytes"
import "math/big"

func (this *Expression) ToStringList() string {
	var buffer bytes.Buffer
	buffer.WriteString("{")
	for i, e := range this.Parts[1:] {
		buffer.WriteString(e.ToString())
		if i != len(this.Parts[1:])-1 {
			buffer.WriteString(", ")
		}
	}
	buffer.WriteString("}")
	return buffer.String()
}

func (this *Expression) EvalLength(es *EvalState) Ex {
	if len(this.Parts) != 2 {
		return this
	}

	list, isList := HeadAssertion(this.Parts[1], "List")
	if isList {
		return &Integer{big.NewInt(int64(len(list.Parts) - 1))}
	}
	return this
}
