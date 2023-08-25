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

func (cmplx *Complex) AsExpr() expreduceapi.Ex {
	iSym := S("I")
	reInt, reIsInt := cmplx.Re.(*Integer)
	imInt, imIsInt := cmplx.Im.(*Integer)
	if reIsInt && reInt.Val.Sign() == 0 {
		if imIsInt && imInt.Val.Int64() == 1 {
			return iSym
		}
		return E(S("Times"), cmplx.Im, iSym)
	}
	if imIsInt && imInt.Val.Int64() == 1 {
		return E(S("Plus"), cmplx.Re, iSym)
	}
	return E(S("Plus"), cmplx.Re, E(S("Times"), cmplx.Im, iSym))
}

func (cmplx *Complex) StringForm(p expreduceapi.ToStringParams) string {
	if p.Form == "FullForm" {
		return fmt.Sprintf("Complex[%v, %v]", cmplx.Re, cmplx.Im)
	}
	return cmplx.AsExpr().StringForm(p)
}

func (cmplx *Complex) IsEqual(other expreduceapi.Ex) string {
	otherConv, otherIsComplex := other.(*Complex)
	if !otherIsComplex {
		return "EQUAL_FALSE"
	}
	if (cmplx.Re.IsEqual(otherConv.Re) != "EQUAL_TRUE") ||
		(cmplx.Im.IsEqual(otherConv.Im) != "EQUAL_TRUE") {
		return "EQUAL_FALSE"
	}
	return "EQUAL_TRUE"
}

func (cmplx *Complex) DeepCopy() expreduceapi.Ex {
	return &Complex{cmplx.Re.DeepCopy(), cmplx.Im.DeepCopy(), cmplx.needsEval}
}

func (cmplx *Complex) Copy() expreduceapi.Ex {
	return cmplx.DeepCopy()
}

func (cmplx *Complex) NeedsEval() bool {
	return cmplx.needsEval
}

func NewComplex(r expreduceapi.Ex, i expreduceapi.Ex) *Complex {
	return &Complex{r, i, true}
}

func (cmplx *Complex) Hash() uint64 {
	h := fnv.New64a()
	h.Write([]byte{82, 226, 223, 39, 113, 26, 149, 249})
	b := make([]byte, 8)
	binary.LittleEndian.PutUint64(b, cmplx.Re.Hash())
	h.Write(b)
	binary.LittleEndian.PutUint64(b, cmplx.Im.Hash())
	h.Write(b)
	return h.Sum64()
}

func (cmplx *Complex) addReal(e expreduceapi.Ex) {
	a, _ := ComputeNumericPart(FoldFnAdd, E(S("Dummy"), cmplx.Re, e))
	cmplx.Re = a
	cmplx.needsEval = true
}

func (cmplx *Complex) addI(i *Integer) {
	cmplx.addReal(i)
}

func (cmplx *Complex) addF(f *Flt) {
	cmplx.addReal(f)
}

func (cmplx *Complex) addR(r *Rational) {
	cmplx.addReal(r)
}

func (cmplx *Complex) addC(c *Complex) {
	a, _ := ComputeNumericPart(FoldFnAdd, E(S("Dummy"), cmplx.Re, c.Re))
	b, _ := ComputeNumericPart(FoldFnAdd, E(S("Dummy"), cmplx.Im, c.Im))
	cmplx.Re = a
	cmplx.Im = b
	cmplx.needsEval = true
}

func (cmplx *Complex) mulReal(e expreduceapi.Ex) {
	a, _ := ComputeNumericPart(FoldFnMul, E(S("Dummy"), cmplx.Re, e))
	b, _ := ComputeNumericPart(FoldFnMul, E(S("Dummy"), cmplx.Im, e))
	cmplx.Re = a
	cmplx.Im = b
	cmplx.needsEval = true
}

func (cmplx *Complex) mulI(i *Integer) {
	cmplx.mulReal(i)
}

func (cmplx *Complex) mulF(f *Flt) {
	cmplx.mulReal(f)
}

func (cmplx *Complex) mulR(r *Rational) {
	cmplx.mulReal(r)
}

func (cmplx *Complex) mulC(c *Complex) {
	// HoldPattern[Complex[x_, y_]*Complex[u_, v_]*rest___] -> Complex[x*u + (y*v)*(-1), x*v + y*u]*rest)
	// cmplx is ugly. Need to refactor.
	// Perhaps create "Calculator" utility??
	// TODO(corywalker) Remove the definition that cmplx implements in code.
	a, _ := ComputeNumericPart(FoldFnMul, E(S("Dummy"), cmplx.Re, c.Re))
	b, _ := ComputeNumericPart(
		FoldFnMul,
		E(S("Dummy"), NewInt(-1), cmplx.Im, c.Im),
	)
	cc, _ := ComputeNumericPart(FoldFnMul, E(S("Dummy"), cmplx.Re, c.Im))
	d, _ := ComputeNumericPart(FoldFnMul, E(S("Dummy"), cmplx.Im, c.Re))
	e, _ := ComputeNumericPart(FoldFnAdd, E(S("Dummy"), a, b))
	f, _ := ComputeNumericPart(FoldFnAdd, E(S("Dummy"), cc, d))
	cmplx.Re = e
	cmplx.Im = f
	cmplx.needsEval = true
}

func (cmplx *Complex) SetNeedsEval(newVal bool) {
	cmplx.needsEval = newVal
}

func (cmplx *Complex) HasReal() bool {
	_, reIsFlt := cmplx.Re.(*Flt)
	_, imIsFlt := cmplx.Im.(*Flt)
	return reIsFlt || imIsFlt
}
