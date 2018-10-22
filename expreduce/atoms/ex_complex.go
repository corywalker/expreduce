package atoms

import (
	"encoding/binary"
	"fmt"
	"hash/fnv"

	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

type Complex struct {
	Re        expreduceapi.Ex
	Im        expreduceapi.Ex
	needsEval bool
}

func (this *Complex) StringForm(p expreduceapi.ToStringParams) string {
	if p.Form == "FullForm" {
		return fmt.Sprintf("Complex[%v, %v]", this.Re, this.Im)
	}
	p.PreviousHead = "System`Plus"
	return fmt.Sprintf("(%v + %v*I)", this.Re.StringForm(p), this.Im.StringForm(p))
}

func (this *Complex) String(esi expreduceapi.EvalStateInterface) string {
	context, ContextPath := DefaultStringFormArgs()
	return this.StringForm(expreduceapi.ToStringParams{
		Form: "InputForm", Context: context, ContextPath: ContextPath, Esi: esi})
}

func (this *Complex) IsEqual(other expreduceapi.Ex) string {
	otherConv, otherIsComplex := other.(*Complex)
	if !otherIsComplex {
		return "EQUAL_FALSE"
	}
	if (this.Re.IsEqual(otherConv.Re) != "EQUAL_TRUE") || (this.Im.IsEqual(otherConv.Im) != "EQUAL_TRUE") {
		return "EQUAL_FALSE"
	}
	return "EQUAL_TRUE"
}

func (this *Complex) DeepCopy() expreduceapi.Ex {
	return &Complex{this.Re.DeepCopy(), this.Im.DeepCopy(), this.needsEval}
}

func (this *Complex) Copy() expreduceapi.Ex {
	return this.DeepCopy()
}

func (this *Complex) NeedsEval() bool {
	return this.needsEval
}

func NewComplex(r expreduceapi.Ex, i expreduceapi.Ex) *Complex {
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

func (this *Complex) addReal(e expreduceapi.Ex) {
	a, _ := ComputeNumericPart(FoldFnAdd, E(S("Dummy"), this.Re, e))
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
	a, _ := ComputeNumericPart(FoldFnAdd, E(S("Dummy"), this.Re, c.Re))
	b, _ := ComputeNumericPart(FoldFnAdd, E(S("Dummy"), this.Im, c.Im))
	this.Re = a
	this.Im = b
	this.needsEval = true
}

func (this *Complex) mulReal(e expreduceapi.Ex) {
	a, _ := ComputeNumericPart(FoldFnMul, E(S("Dummy"), this.Re, e))
	b, _ := ComputeNumericPart(FoldFnMul, E(S("Dummy"), this.Im, e))
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
	a, _ := ComputeNumericPart(FoldFnMul, E(S("Dummy"), this.Re, c.Re))
	b, _ := ComputeNumericPart(FoldFnMul, E(S("Dummy"), NewInt(-1), this.Im, c.Im))
	cc, _ := ComputeNumericPart(FoldFnMul, E(S("Dummy"), this.Re, c.Im))
	d, _ := ComputeNumericPart(FoldFnMul, E(S("Dummy"), this.Im, c.Re))
	e, _ := ComputeNumericPart(FoldFnAdd, E(S("Dummy"), a, b))
	f, _ := ComputeNumericPart(FoldFnAdd, E(S("Dummy"), cc, d))
	this.Re = e
	this.Im = f
	this.needsEval = true
}
