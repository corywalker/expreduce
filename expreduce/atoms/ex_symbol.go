package atoms

import (
	"fmt"
	"hash/fnv"
	"sort"
	"strings"

	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

// Symbol represents a symbol in Expreduce. Symbols are defined by a
// string-based name.
type Symbol struct {
	Name       string
	cachedHash uint64
}

func formatSymName(name string, params expreduceapi.ToStringParams) string {
	if params.Form == "TeXForm" {
		if name == "E" {
			return "e"
		}
		if name == "I" {
			return "i"
		}
		if name == "Pi" {
			return "\\pi"
		}
		if name == "Infinity" {
			return "\\infty"
		}
		if name == "ω" {
			return "\\omega"
		}
		if name == "Ω" {
			return "\\Omega"
		}
		if len(name) > 1 {
			return fmt.Sprintf("\\text{%v}", name)
		}
	}
	return fmt.Sprintf("%v", name)
}

func (sym *Symbol) StringForm(params expreduceapi.ToStringParams) string {
	if len(sym.Name) == 0 {
		return "<EMPTYSYM>"
	}
	if strings.HasPrefix(sym.Name, params.Context.GetValue()) {
		return formatSymName(sym.Name[len(params.Context.GetValue()):], params)
	}
	for _, pathPart := range params.ContextPath.GetParts()[1:] {
		path := pathPart.(*String).Val
		if strings.HasPrefix(sym.Name, path) {
			return formatSymName(sym.Name[len(path):], params)
		}
	}
	return formatSymName(sym.Name, params)
}

func (sym *Symbol) String() string {
	return sym.StringForm(defaultStringParams())
}

func (sym *Symbol) IsEqual(other expreduceapi.Ex) string {
	otherConv, ok := other.(*Symbol)
	if !ok {
		return "EQUAL_UNK"
	}
	if sym.Name == "System`False" && otherConv.Name == "System`True" {
		return "EQUAL_FALSE"
	}
	if sym.Name == "System`True" && otherConv.Name == "System`False" {
		return "EQUAL_FALSE"
	}
	if sym.Name != otherConv.Name {
		return "EQUAL_UNK"
	}
	return "EQUAL_TRUE"
}

func (sym *Symbol) DeepCopy() expreduceapi.Ex {
	symcopy := *sym
	return &symcopy
}

func (sym *Symbol) Copy() expreduceapi.Ex {
	return sym
}

func (sym *Symbol) Attrs(
	dm expreduceapi.DefinitionMap,
) expreduceapi.Attributes {
	def, isDef := dm.Get(sym.Name)
	if !isDef {
		return expreduceapi.Attributes{}
	}
	return def.Attributes
}

func (sym *Symbol) Default(dm expreduceapi.DefinitionMap) expreduceapi.Ex {
	def, isDef := dm.Get(sym.Name)
	if !isDef {
		return nil
	}
	return def.DefaultExpr
}

func StringsToAttributes(strings []string) expreduceapi.Attributes {
	attrs := expreduceapi.Attributes{}
	for _, s := range strings {
		if s == "Orderless" {
			attrs.Orderless = true
		}
		if s == "Flat" {
			attrs.Flat = true
		}
		if s == "OneIdentity" {
			attrs.OneIdentity = true
		}
		if s == "Listable" {
			attrs.Listable = true
		}
		if s == "Constant" {
			attrs.Constant = true
		}
		if s == "NumericFunction" {
			attrs.NumericFunction = true
		}
		if s == "Protected" {
			attrs.Protected = true
		}
		if s == "Locked" {
			attrs.Locked = true
		}
		if s == "ReadProtected" {
			attrs.ReadProtected = true
		}
		if s == "HoldFirst" {
			attrs.HoldFirst = true
		}
		if s == "HoldRest" {
			attrs.HoldRest = true
		}
		if s == "HoldAll" {
			attrs.HoldAll = true
		}
		if s == "HoldAllComplete" {
			attrs.HoldAllComplete = true
		}
		if s == "NHoldFirst" {
			attrs.NHoldFirst = true
		}
		if s == "NHoldRest" {
			attrs.NHoldRest = true
		}
		if s == "NHoldAll" {
			attrs.NHoldAll = true
		}
		if s == "SequenceHold" {
			attrs.SequenceHold = true
		}
		if s == "Temporary" {
			attrs.Temporary = true
		}
		if s == "Stub" {
			attrs.Stub = true
		}
	}
	return attrs
}

func AttrsToStrings(sym *expreduceapi.Attributes) []string {
	var strings []string
	if sym.Orderless {
		strings = append(strings, "Orderless")
	}
	if sym.Flat {
		strings = append(strings, "Flat")
	}
	if sym.OneIdentity {
		strings = append(strings, "OneIdentity")
	}
	if sym.Listable {
		strings = append(strings, "Listable")
	}
	if sym.Constant {
		strings = append(strings, "Constant")
	}
	if sym.NumericFunction {
		strings = append(strings, "NumericFunction")
	}
	if sym.Protected {
		strings = append(strings, "Protected")
	}
	if sym.Locked {
		strings = append(strings, "Locked")
	}
	if sym.ReadProtected {
		strings = append(strings, "ReadProtected")
	}
	if sym.HoldFirst {
		strings = append(strings, "HoldFirst")
	}
	if sym.HoldRest {
		strings = append(strings, "HoldRest")
	}
	if sym.HoldAll {
		strings = append(strings, "HoldAll")
	}
	if sym.HoldAllComplete {
		strings = append(strings, "HoldAllComplete")
	}
	if sym.NHoldFirst {
		strings = append(strings, "NHoldFirst")
	}
	if sym.NHoldRest {
		strings = append(strings, "NHoldRest")
	}
	if sym.NHoldAll {
		strings = append(strings, "NHoldAll")
	}
	if sym.SequenceHold {
		strings = append(strings, "SequenceHold")
	}
	if sym.Temporary {
		strings = append(strings, "Temporary")
	}
	if sym.Stub {
		strings = append(strings, "Stub")
	}

	sort.Strings(strings)
	return strings
}

func AttrsToSymList(
	sym *expreduceapi.Attributes,
) expreduceapi.ExpressionInterface {
	toReturn := E(S("List"))
	for _, s := range AttrsToStrings(sym) {
		toReturn.AppendEx(S(s))
	}
	return toReturn
}

func (sym *Symbol) NeedsEval() bool {
	return false
}

func (sym *Symbol) Hash() uint64 {
	if sym.cachedHash > 0 {
		return sym.cachedHash
	}
	h := fnv.New64a()
	h.Write([]byte{107, 10, 247, 23, 33, 221, 163, 156})
	h.Write([]byte(sym.Name))
	sym.cachedHash = h.Sum64()
	return h.Sum64()
}

func ContainsSymbol(e expreduceapi.Ex, name string) bool {
	asSym, isSym := e.(*Symbol)
	if isSym {
		return asSym.Name == name
	}
	asExpr, isExpr := e.(expreduceapi.ExpressionInterface)
	if isExpr {
		for _, part := range asExpr.GetParts() {
			if ContainsSymbol(part, name) {
				return true
			}
		}
	}
	return false
}

func NewSymbol(name string) *Symbol {
	return &Symbol{Name: name}
}

func S(name string) expreduceapi.Ex {
	return NewSymbol("System`" + name)
}
