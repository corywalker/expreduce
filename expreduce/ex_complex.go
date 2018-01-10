package expreduce

import "fmt"
import "math/big"
import "hash/fnv"

type Complex struct {
	Re       *big.Int
	Im       *big.Int
	needsEval bool
}

func (this *Complex) Eval(es *EvalState) Ex {
	if this.Im.Cmp(big.NewInt(0)) == 0 {
		return NewInteger(this.Re)
	}
	this.needsEval = false
	return this
}

func (this *Complex) StringForm(params ToStringParams) string {
	if params.form == "FullForm" {
		return fmt.Sprintf("Complex[%d, %d]", this.Re, this.Im)
	}
	return fmt.Sprintf("(%d + %d*I)", this.Re, this.Im)
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
	if (this.Re.Cmp(otherConv.Re) != 0) || (this.Im.Cmp(otherConv.Im) != 0) {
		return "EQUAL_FALSE"
	}
	return "EQUAL_TRUE"
}

func (this *Complex) DeepCopy() Ex {
	tmpn := big.NewInt(0)
	tmpn.Set(this.Re)
	tmpd := big.NewInt(0)
	tmpd.Set(this.Im)
	return &Complex{tmpn, tmpd, this.needsEval}
}

func (this *Complex) Copy() Ex {
	return this.DeepCopy()
}

func (this *Complex) NeedsEval() bool {
	return this.needsEval
}

func NewComplex(r *big.Int, i *big.Int) *Complex {
	return &Complex{r, i, true}
}

func (this *Complex) Hash() uint64 {
	h := fnv.New64a()
	h.Write([]byte{82, 226, 223, 39, 113, 26, 149, 249})
	nBytes, _ := this.Re.MarshalText()
	h.Write(nBytes)
	dBytes, _ := this.Im.MarshalText()
	h.Write(dBytes)
	return h.Sum64()
}
