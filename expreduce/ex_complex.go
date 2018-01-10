package expreduce

import "fmt"
import "hash/fnv"
import "encoding/binary"

type Complex struct {
	Re       Ex
	Im       Ex
	needsEval bool
}

func (this *Complex) Eval(es *EvalState) Ex {
	if IsSameQ(this.Im, NewInt(0), &es.CASLogger) {
		return this.Re
	}
	this.needsEval = false
	return this
}

func (this *Complex) StringForm(p ToStringParams) string {
	if p.form == "FullForm" {
		return fmt.Sprintf("Complex[%v, %v]", this.Re, this.Im)
	}
	p.previousHead = "System`Plus"
	return fmt.Sprintf("(%v + %v*I)", this.Re.StringForm(p), this.Im.StringForm(p))
}

func (this *Complex) String() string {
	context, contextPath := DefaultStringFormArgs()
	return this.StringForm(ToStringParams{form: "InputForm", context: context, contextPath: contextPath})
}

func (this *Complex) IsEqual(other Ex, cl *CASLogger) string {
	otherConv, otherIsComplex := other.(*Complex)
	if !otherIsComplex {
		return "EQUAL_FALSE"
	}
	if (this.Re.IsEqual(otherConv.Re, cl) != "EQUAL_TRUE") || (this.Im.IsEqual(otherConv.Im, cl) != "EQUAL_TRUE") {
		return "EQUAL_FALSE"
	}
	return "EQUAL_TRUE"
}

func (this *Complex) DeepCopy() Ex {
	return &Complex{this.Re.DeepCopy(), this.Im.DeepCopy(), this.needsEval}
}

func (this *Complex) Copy() Ex {
	return this.DeepCopy()
}

func (this *Complex) NeedsEval() bool {
	return this.needsEval
}

func NewComplex(r Ex, i Ex) *Complex {
	return &Complex{r, i, true}
}

func (this *Complex) Hash() uint64 {
	h := fnv.New64a()
	h.Write([]byte{82, 226, 223, 39, 113, 26, 149, 249})
	b := make([]byte, 8)
	binary.LittleEndian.PutUint64(b, this.Re.Hash())
	h.Write(b)
	binary.LittleEndian.PutUint64(b, this.Im.Hash())
	h.Write(b)
	return h.Sum64()
}
