package expreduce

import "bytes"

type Def struct {
	downvalues []Expression
	attributes Attributes
	defaultExpr Ex

	// A function defined here will override downvalues.
	legacyEvalFn (func(*Expression, *EvalState) Ex)
}

func CopyDefs(in map[string]Def) map[string]Def {
	out := make(map[string]Def)
	for k, v := range in {
		newDef := Def{}
		for _, rule := range v.downvalues {
			newDef.downvalues = append(newDef.downvalues, *rule.DeepCopy().(*Expression))
		}
		out[k] = newDef
	}
	return out
}

func (this *Def) String() string {
	var buffer bytes.Buffer
	buffer.WriteString("{")
	for i, e := range this.downvalues {
		buffer.WriteString(e.String())
		if i != len(this.downvalues)-1 {
			buffer.WriteString("\n")
		}
	}
	buffer.WriteString("}")
	return buffer.String()
}
