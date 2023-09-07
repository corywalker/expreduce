package atoms

import (
	"bytes"
	"encoding/binary"
	"hash/fnv"
	"sync/atomic"

	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

type Expression struct {
	Parts                 []expreduceapi.Ex
	needsEval             bool
	correctlyInstantiated bool
	EvaledHash            uint64
	CachedHash            uint64
}

// HeadAssertion checks if the Ex is an Expression of with a head of 'head'.
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

func HeadExAssertion(
	ex expreduceapi.Ex,
	head expreduceapi.Ex,
	cl expreduceapi.LoggingInterface,
) (*Expression, bool) {
	expr, isExpr := ex.(*Expression)
	if isExpr {
		if IsSameQ(head, expr.GetParts()[0]) {
			return expr, true
		}
	}
	return nil, false
}

func OperatorAssertion(
	ex expreduceapi.Ex,
	opHead string,
) (*Expression, *Expression, bool) {
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

func (thisExpr *Expression) PropagateConditionals() (*Expression, bool) {
	foundCond := false
	for _, e := range thisExpr.GetParts()[1:] {
		if cond, isCond := HeadAssertion(e, "System`ConditionalExpression"); isCond {
			if len(cond.GetParts()) == 3 {
				foundCond = true
				break
			}
		}
	}
	if foundCond {
		resEx := E(thisExpr.GetParts()[0])
		resCond := E(S("And"))
		for _, e := range thisExpr.GetParts()[1:] {
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
	return thisExpr, false
}

func (thisExpr *Expression) StringForm(
	params expreduceapi.ToStringParams,
) string {
	headAsSym, isHeadSym := thisExpr.GetParts()[0].(*Symbol)
	fullForm := false
	if isHeadSym && !fullForm && params.Esi != nil {
		res, ok := "", false
		headStr := headAsSym.Name
		toStringFn, hasToStringFn := params.Esi.GetStringFn(headStr)
		if hasToStringFn {
			ok, res = toStringFn(thisExpr, params)
		}
		if ok {
			return res
		}
	}

	if len(thisExpr.GetParts()) == 2 && isHeadSym &&
		(headAsSym.Name == "System`InputForm" ||
			headAsSym.Name == "System`FullForm" ||
			headAsSym.Name == "System`TraditionalForm" ||
			headAsSym.Name == "System`TeXForm" ||
			headAsSym.Name == "System`StandardForm" ||
			headAsSym.Name == "System`OutputForm") {
		mutatedParams := params
		mutatedParams.Form = headAsSym.Name[7:]
		return thisExpr.GetParts()[1].StringForm(mutatedParams)
	}

	// Default printing format
	var buffer bytes.Buffer
	buffer.WriteString(thisExpr.GetParts()[0].StringForm(params))
	buffer.WriteString("[")
	params.PreviousHead = "<TOPLEVEL>"
	for i, e := range thisExpr.GetParts() {
		if i == 0 {
			continue
		}
		buffer.WriteString(e.StringForm(params))
		if i != len(thisExpr.GetParts())-1 {
			buffer.WriteString(", ")
		}
	}
	buffer.WriteString("]")
	return buffer.String()
}

func (thisExpr *Expression) String() string {
	return thisExpr.StringForm(defaultStringParams())
}

func (thisExpr *Expression) IsEqual(otherEx expreduceapi.Ex) string {
	other, ok := otherEx.(*Expression)
	if !ok {
		return "EQUAL_UNK"
	}

	if len(thisExpr.GetParts()) != len(other.GetParts()) {
		return "EQUAL_UNK"
	}
	for i := range thisExpr.GetParts() {
		res := thisExpr.GetParts()[i].IsEqual(other.GetParts()[i])
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

func (thisExpr *Expression) DeepCopy() expreduceapi.Ex {
	var thisExprcopy = NewEmptyExpression()
	for i := range thisExpr.GetParts() {
		thisExprcopy.AppendEx(thisExpr.GetParts()[i].DeepCopy())
	}
	thisExprcopy.needsEval = thisExpr.needsEval
	thisExprcopy.correctlyInstantiated = thisExpr.correctlyInstantiated
	thisExprcopy.EvaledHash = thisExpr.EvaledHash
	thisExprcopy.CachedHash = thisExpr.CachedHash
	return thisExprcopy
}

func ShallowCopy(thisExprExprInt expreduceapi.ExpressionInterface) *Expression {
	thisExpr := thisExprExprInt.(*Expression)
	var thisExprcopy = NewEmptyExpression()
	thisExprcopy.Parts = append([]expreduceapi.Ex{}, thisExpr.GetParts()...)
	thisExprcopy.needsEval = thisExpr.needsEval
	thisExprcopy.correctlyInstantiated = thisExpr.correctlyInstantiated
	thisExprcopy.EvaledHash = thisExpr.EvaledHash
	thisExprcopy.CachedHash = thisExpr.CachedHash
	return thisExprcopy
}

func (thisExpr *Expression) Copy() expreduceapi.Ex {
	var thisExprcopy = newEmptyExpressionOfLength(len(thisExpr.GetParts()))
	for i := range thisExpr.GetParts() {
		thisExprcopy.GetParts()[i] = thisExpr.GetParts()[i].Copy()
	}
	thisExprcopy.needsEval = thisExpr.needsEval
	thisExprcopy.correctlyInstantiated = thisExpr.correctlyInstantiated
	thisExprcopy.EvaledHash = thisExpr.EvaledHash
	thisExprcopy.CachedHash = thisExpr.CachedHash
	return thisExprcopy
}

// Implement the sort.Interface
func (thisExpr *Expression) Len() int {
	return len(thisExpr.GetParts()) - 1
}

func (thisExpr *Expression) Less(i, j int) bool {
	return ExOrder(thisExpr.GetParts()[i+1], thisExpr.GetParts()[j+1]) == 1
}

func (thisExpr *Expression) Swap(i, j int) {
	thisExpr.GetParts()[j+1], thisExpr.GetParts()[i+1] = thisExpr.GetParts()[i+1], thisExpr.GetParts()[j+1]
}

func (thisExpr *Expression) AppendEx(e expreduceapi.Ex) {
	thisExpr.Parts = append(thisExpr.Parts, e)
}

func (thisExpr *Expression) AppendExArray(e []expreduceapi.Ex) {
	thisExpr.Parts = append(thisExpr.Parts, e...)
}

func (thisExpr *Expression) NeedsEval() bool {
	return thisExpr.needsEval
}

func (thisExpr *Expression) SetNeedsEval(newVal bool) {
	thisExpr.needsEval = newVal
}

func (thisExpr *Expression) Hash() uint64 {
	if atomic.LoadUint64(&thisExpr.CachedHash) > 0 {
		return thisExpr.CachedHash
	}
	h := fnv.New64a()
	h.Write([]byte{72, 5, 244, 86, 5, 210, 69, 30})
	b := make([]byte, 8)
	for _, part := range thisExpr.GetParts() {
		binary.LittleEndian.PutUint64(b, part.Hash())
		h.Write(b)
	}
	atomic.StoreUint64(&thisExpr.CachedHash, h.Sum64())
	return h.Sum64()
}

func (thisExpr *Expression) HeadStr() string {
	sym, isSym := thisExpr.GetParts()[0].(*Symbol)
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

func newEmptyExpressionOfLength(n int) *Expression {
	return &Expression{
		Parts:                 make([]expreduceapi.Ex, n),
		needsEval:             true,
		correctlyInstantiated: true,
	}
}

// NewStringList transforms a list of strings in Go format into Expreduce format.
func NewStringList(items []string) *Expression {
	list := NewHead("System`List")
	for _, item := range items {
		list.AppendEx(NewString(item))
	}
	return list
}

func (thisExpr *Expression) GetParts() []expreduceapi.Ex {
	return thisExpr.Parts
}

func (thisExpr *Expression) GetPart(i int) expreduceapi.Ex {
	return thisExpr.Parts[i]
}

func (thisExpr *Expression) SetParts(newParts []expreduceapi.Ex) {
	thisExpr.Parts = newParts
}

func (thisExpr *Expression) ClearHashes() {
	thisExpr.EvaledHash = 0
	thisExpr.CachedHash = 0
}
