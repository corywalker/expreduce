package atoms

import (
	"bytes"
	"fmt"
	"hash/fnv"
	"math/big"
	"strings"

	"github.com/corywalker/expreduce/expreduce/parser/parens"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

// Flt represents a floating point number in Expreduce. The values are
// represented by big.Float internally.
type Flt struct {
	Val *big.Float
}

func (flt *Flt) StringForm(params expreduceapi.ToStringParams) string {
	var buffer bytes.Buffer
	useParens := false
	if flt.Val.Cmp(big.NewFloat(0)) < 0 {
		if parens.NeedsParens("System`Times", params.PreviousHead) {
			useParens = true
			if params.Form == "TeXForm" {
				buffer.WriteString("{")
			}
			buffer.WriteString("(")
		}
	}
	buffer.WriteString(fmt.Sprintf("%.6g", flt.Val))
	if bytes.IndexRune(buffer.Bytes(), '.') == -1 {
		buffer.WriteString(".")
	}
	if useParens {
		buffer.WriteString(")")
		if params.Form == "TeXForm" {
			buffer.WriteString("}")
		}
	}
	return buffer.String()
}

func (flt *Flt) IsEqual(other expreduceapi.Ex) string {
	otherConv, ok := other.(*Flt)
	if !ok {
		otherInteger, ok := other.(*Integer)
		if ok {
			otherAsFlt := big.NewFloat(0)
			otherAsFlt.SetInt(otherInteger.Val)
			if otherAsFlt.Cmp(flt.Val) == 0 {
				return "EQUAL_TRUE"
			}
		}
		return "EQUAL_UNK"
	}
	fltStr := fmt.Sprintf("%.14g", flt.Val)
	otherStr := fmt.Sprintf("%.14g", otherConv.Val)
	if strings.Compare(fltStr, otherStr) != 0 {
		return "EQUAL_FALSE"
	}
	return "EQUAL_TRUE"
}

func (flt *Flt) DeepCopy() expreduceapi.Ex {
	tmp := big.NewFloat(0)
	tmp.Copy(flt.Val)
	return NewReal(tmp)
}

func (flt *Flt) Copy() expreduceapi.Ex {
	return flt.DeepCopy()
}

func IntegerToFlt(i *Integer) (*Flt, bool) {
	newfloat := big.NewFloat(0)
	newfloat.SetInt(i.Val)
	return NewReal(newfloat), true
}

func RationalToFlt(r *Rational) (*Flt, bool) {
	newfloat := big.NewFloat(0)
	newfloat.SetRat(r.asBigRat())
	return NewReal(newfloat), true
}

func (flt *Flt) NeedsEval() bool {
	return false
}

func (flt *Flt) Hash() uint64 {
	h := fnv.New64a()
	h.Write([]byte{195, 244, 76, 249, 227, 115, 88, 251})
	bytes, _ := flt.Val.MarshalText()
	h.Write(bytes)
	return h.Sum64()
}

func (flt *Flt) addI(i *Integer) {
	flt.Val.Add(flt.Val, i.asBigFloat())
}

func (flt *Flt) addR(r *Rational) {
	flt.Val.Add(flt.Val, r.asBigFloat())
}

func (flt *Flt) addF(f *Flt) {
	flt.Val.Add(flt.Val, f.Val)
}

func (flt *Flt) mulI(i *Integer) {
	flt.Val.Mul(flt.Val, i.asBigFloat())
}

func (flt *Flt) mulR(r *Rational) {
	flt.Val.Mul(flt.Val, r.asBigFloat())
}

func (flt *Flt) mulF(f *Flt) {
	flt.Val.Mul(flt.Val, f.Val)
}

func NewReal(v *big.Float) *Flt {
	return &Flt{v}
}
