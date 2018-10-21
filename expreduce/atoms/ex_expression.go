package atoms

import (
	"bytes"
	"encoding/binary"
	"flag"
	"hash/fnv"
	"sync/atomic"

	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

var printevals = flag.Bool("printevals", false, "")
var checkhashes = flag.Bool("checkhashes", false, "")

type Expression struct {
	Parts                 []expreduceapi.Ex
	needsEval             bool
	correctlyInstantiated bool
	evaledHash            uint64
	cachedHash            uint64
}

// Deprecated in favor of headExAssertion
func HeadAssertion(ex expreduceapi.Ex, head string) (*Expression, bool) {
	expr, isExpr := ex.(*Expression)
	if isExpr {
		sym, isSym := expr.GetParts()[0].(*Symbol)
		if isSym {
			if sym.Name == head {
				return expr, true
			}
		}
	}
	return nil, false
}

func headExAssertion(ex expreduceapi.Ex, head expreduceapi.Ex, cl expreduceapi.LoggingInterface) (*Expression, bool) {
	expr, isExpr := ex.(*Expression)
	if isExpr {
		if IsSameQ(head, expr.GetParts()[0], cl) {
			return expr, true
		}
	}
	return nil, false
}

func OperatorAssertion(ex expreduceapi.Ex, opHead string) (*Expression, *Expression, bool) {
	expr, isExpr := ex.(*Expression)
	if isExpr {
		headExpr, headIsExpr := expr.GetParts()[0].(*Expression)
		if headIsExpr {
			sym, isSym := headExpr.GetParts()[0].(*Symbol)
			if isSym {
				if sym.Name == opHead {
					return expr, headExpr, true
				}
			}
		}
	}
	return nil, nil, false
}

func (this *Expression) propagateConditionals() (*Expression, bool) {
	foundCond := false
	for _, e := range this.GetParts()[1:] {
		if cond, isCond := HeadAssertion(e, "System`ConditionalExpression"); isCond {
			if len(cond.GetParts()) == 3 {
				foundCond = true
				break
			}
		}
	}
	if foundCond {
		resEx := E(this.GetParts()[0])
		resCond := E(S("And"))
		for _, e := range this.GetParts()[1:] {
			if cond, isCond := HeadAssertion(e, "System`ConditionalExpression"); isCond {
				if len(cond.GetParts()) == 3 {
					resEx.AppendEx(cond.GetParts()[1].DeepCopy())
					resCond.AppendEx(cond.GetParts()[2].DeepCopy())
					continue
				}
			}
			resEx.AppendEx(e.DeepCopy())
		}
		return E(S("ConditionalExpression"), resEx, resCond), true
	}
	return this, false
}

func (this *Expression) StringForm(params expreduceapi.ToStringParams) string {
	headAsSym, isHeadSym := this.GetParts()[0].(*Symbol)
	fullForm := false
	if isHeadSym && !fullForm {
		res, ok := "", false
		headStr := headAsSym.Name
		toStringFn, hasToStringFn := params.Esi.GetStringFn(headStr)
		if hasToStringFn {
			ok, res = toStringFn(this, params)
		}
		if ok {
			return res
		}
	}

	if len(this.GetParts()) == 2 && isHeadSym && (headAsSym.Name == "System`InputForm" ||
		headAsSym.Name == "System`FullForm" ||
		headAsSym.Name == "System`TraditionalForm" ||
		headAsSym.Name == "System`TeXForm" ||
		headAsSym.Name == "System`StandardForm" ||
		headAsSym.Name == "System`OutputForm") {
		mutatedParams := params
		mutatedParams.Form = headAsSym.Name[7:]
		return this.GetParts()[1].StringForm(mutatedParams)
	}

	// Default printing format
	var buffer bytes.Buffer
	buffer.WriteString(this.GetParts()[0].StringForm(params))
	buffer.WriteString("[")
	params.PreviousHead = "<TOPLEVEL>"
	for i, e := range this.GetParts() {
		if i == 0 {
			continue
		}
		buffer.WriteString(e.StringForm(params))
		if i != len(this.GetParts())-1 {
			buffer.WriteString(", ")
		}
	}
	buffer.WriteString("]")
	return buffer.String()
}

func (this *Expression) String(esi expreduceapi.EvalStateInterface) string {
	context, ContextPath := DefaultStringFormArgs()
	return this.StringForm(expreduceapi.ToStringParams{
		Form: "InputForm", Context: context, ContextPath: ContextPath, Esi: esi})
}

func (this *Expression) IsEqual(otherEx expreduceapi.Ex) string {
	other, ok := otherEx.(*Expression)
	if !ok {
		return "EQUAL_UNK"
	}

	if len(this.GetParts()) != len(other.GetParts()) {
		return "EQUAL_UNK"
	}
	for i := range this.GetParts() {
		res := this.GetParts()[i].IsEqual(other.GetParts()[i])
		switch res {
		case "EQUAL_FALSE":
			return "EQUAL_UNK"
		case "EQUAL_TRUE":
		case "EQUAL_UNK":
			return "EQUAL_UNK"
		}
	}
	return "EQUAL_TRUE"
}

func (this *Expression) DeepCopy() expreduceapi.Ex {
	var thiscopy = NewEmptyExpression()
	for i := range this.GetParts() {
		thiscopy.AppendEx(this.GetParts()[i].DeepCopy())
	}
	thiscopy.needsEval = this.needsEval
	thiscopy.correctlyInstantiated = this.correctlyInstantiated
	thiscopy.evaledHash = this.evaledHash
	thiscopy.cachedHash = this.cachedHash
	return thiscopy
}

func ShallowCopy(thisExprInt expreduceapi.ExpressionInterface) *Expression {
	this := thisExprInt.(*Expression)
	var thiscopy = NewEmptyExpression()
	thiscopy.Parts = append([]expreduceapi.Ex{}, this.GetParts()...)
	thiscopy.needsEval = this.needsEval
	thiscopy.correctlyInstantiated = this.correctlyInstantiated
	thiscopy.evaledHash = this.evaledHash
	thiscopy.cachedHash = this.cachedHash
	return thiscopy
}

func (this *Expression) Copy() expreduceapi.Ex {
	var thiscopy = NewEmptyExpressionOfLength(len(this.GetParts()))
	for i := range this.GetParts() {
		thiscopy.GetParts()[i] = this.GetParts()[i].Copy()
	}
	thiscopy.needsEval = this.needsEval
	thiscopy.correctlyInstantiated = this.correctlyInstantiated
	thiscopy.evaledHash = this.evaledHash
	thiscopy.cachedHash = this.cachedHash
	return thiscopy
}

// Implement the sort.Interface
func (this *Expression) Len() int {
	return len(this.GetParts()) - 1
}

func (this *Expression) Less(i, j int) bool {
	return ExOrder(this.GetParts()[i+1], this.GetParts()[j+1]) == 1
}

func (this *Expression) Swap(i, j int) {
	this.GetParts()[j+1], this.GetParts()[i+1] = this.GetParts()[i+1], this.GetParts()[j+1]
}

func (this *Expression) AppendEx(e expreduceapi.Ex) {
	this.Parts = append(this.Parts, e)
}

func (this *Expression) AppendExArray(e []expreduceapi.Ex) {
	this.Parts = append(this.Parts, e...)
}

func (this *Expression) NeedsEval() bool {
	return this.needsEval
}

func (this *Expression) Hash() uint64 {
	if atomic.LoadUint64(&this.cachedHash) > 0 {
		return this.cachedHash
	}
	h := fnv.New64a()
	h.Write([]byte{72, 5, 244, 86, 5, 210, 69, 30})
	b := make([]byte, 8)
	for _, part := range this.GetParts() {
		binary.LittleEndian.PutUint64(b, part.Hash())
		h.Write(b)
	}
	atomic.StoreUint64(&this.cachedHash, h.Sum64())
	return h.Sum64()
}

func (this *Expression) HeadStr() string {
	sym, isSym := this.GetParts()[0].(*Symbol)
	if isSym {
		return sym.Name
	}
	return ""
}

func NewExpression(parts []expreduceapi.Ex) *Expression {
	return &Expression{
		Parts:                 parts,
		needsEval:             true,
		correctlyInstantiated: true,
	}
}

func E(parts ...expreduceapi.Ex) *Expression {
	return NewExpression(parts)
}

func NewHead(head string) *Expression {
	return NewExpression([]expreduceapi.Ex{NewSymbol(head)})
}

func NewEmptyExpression() *Expression {
	return &Expression{
		needsEval:             true,
		correctlyInstantiated: true,
	}
}

func NewEmptyExpressionOfLength(n int) *Expression {
	return &Expression{
		Parts:                 make([]expreduceapi.Ex, n),
		needsEval:             true,
		correctlyInstantiated: true,
	}
}

func (this *Expression) GetParts() []expreduceapi.Ex {
	return this.Parts
}

func (this *Expression) SetParts(newParts []expreduceapi.Ex) {
	this.Parts = newParts
}

func (this *Expression) ClearHashes() {
	this.evaledHash = 0
	this.cachedHash = 0
}
