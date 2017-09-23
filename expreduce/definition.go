package expreduce

import "bytes"

type DownValue struct {
	rule        *Expression
	specificity int
}

type Def struct {
	downvalues  []DownValue
	attributes  Attributes
	defaultExpr Ex

	// A function defined here will override downvalues.
	legacyEvalFn (func(*Expression, *EvalState) Ex)
}

func CopyDefs(in map[string]Def) map[string]Def {
	out := make(map[string]Def)
	for k, v := range in {
		newDef := Def{}
		for _, dv := range v.downvalues {
			newDv := DownValue{
				rule:        dv.rule.DeepCopy().(*Expression),
				specificity: dv.specificity,
			}
			newDef.downvalues = append(newDef.downvalues, newDv)
		}
		out[k] = newDef
	}
	return out
}

func (this *Def) String() string {
	var buffer bytes.Buffer
	buffer.WriteString("{")
	for i, dv := range this.downvalues {
		buffer.WriteString(dv.rule.String())
		if i != len(this.downvalues)-1 {
			buffer.WriteString("\n")
		}
	}
	buffer.WriteString("}")
	return buffer.String()
}

func (def *Def) StringForm(form string, context *String, contextPath *Expression) string {
	var buffer bytes.Buffer
	buffer.WriteString("{")
	for i, dv := range def.downvalues {
		buffer.WriteString(dv.rule.StringForm(form, context, contextPath))
		if i != len(def.downvalues)-1 {
			buffer.WriteString("\n")
		}
	}
	buffer.WriteString("}")
	return buffer.String()
}
