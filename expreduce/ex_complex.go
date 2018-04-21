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
	this.Re = this.Re.Eval(es)
	this.Im = this.Im.Eval(es)
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

func (this *Complex) addReal(e Ex) {
	a, _ := computeNumericPart(FoldFnAdd, E(S("Dummy"), this.Re, e))
	this.Re = a
	this.needsEval = true
}

func (this *Complex) AddI(i *Integer) {
	this.addReal(i)
}

func (this *Complex) AddF(f *Flt) {
	this.addReal(f)
}

func (this *Complex) AddR(r *Rational) {
	this.addReal(r)
}

func (this *Complex) AddC(c *Complex) {
	a, _ := computeNumericPart(FoldFnAdd, E(S("Dummy"), this.Re, c.Re))
	b, _ := computeNumericPart(FoldFnAdd, E(S("Dummy"), this.Im, c.Im))
	this.Re = a
	this.Im = b
	this.needsEval = true
}

func (this *Complex) mulReal(e Ex) {
	a, _ := computeNumericPart(FoldFnMul, E(S("Dummy"), this.Re, e))
	b, _ := computeNumericPart(FoldFnMul, E(S("Dummy"), this.Im, e))
	this.Re = a
	this.Im = b
	this.needsEval = true
}

func (this *Complex) MulI(i *Integer) {
	this.mulReal(i)
}

func (this *Complex) MulF(f *Flt) {
	this.mulReal(f)
}

func (this *Complex) MulR(r *Rational) {
	this.mulReal(r)
}

func (this *Complex) MulC(c *Complex) {
	// HoldPattern[Complex[x_, y_]*Complex[u_, v_]*rest___] -> Complex[x*u + (y*v)*(-1), x*v + y*u]*rest)
	// This is ugly. Need to refactor.
	// Perhaps create "Calculator" utility??
	// TODO(corywalker) Remove the definition that this implements in code.
	a, _ := computeNumericPart(FoldFnMul, E(S("Dummy"), this.Re, c.Re))
	b, _ := computeNumericPart(FoldFnMul, E(S("Dummy"), NewInt(-1), this.Im, c.Im))
	cc, _ := computeNumericPart(FoldFnMul, E(S("Dummy"), this.Re, c.Im))
	d, _ := computeNumericPart(FoldFnMul, E(S("Dummy"), this.Im, c.Re))
	e, _ := computeNumericPart(FoldFnAdd, E(S("Dummy"), a, b))
	f, _ := computeNumericPart(FoldFnAdd, E(S("Dummy"), cc, d))
	this.Re = e
	this.Im = f
	this.needsEval = true
}
