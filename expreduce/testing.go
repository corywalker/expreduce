package expreduce

import (
	"bytes"
	"testing"

	"github.com/corywalker/expreduce/expreduce/atoms"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
	"github.com/stretchr/testify/assert"
)

type TestDesc struct {
	module string
	def    Definition
	desc   string
}

type TestInstruction interface {
	Run(t *testing.T, es expreduceapi.EvalStateInterface, td TestDesc) bool
}

type SameTest struct {
	Out string
	In  string
}

func (this *SameTest) Run(t *testing.T, es expreduceapi.EvalStateInterface, td TestDesc) bool {
	return CasAssertDescSame(t, es, this.Out, this.In, td.desc)
}

type StringTest struct {
	Out string
	In  string
}

func (this *StringTest) Run(t *testing.T, es expreduceapi.EvalStateInterface, td TestDesc) bool {
	return assert.Equal(t, this.Out, EasyRun(this.In, es), td.desc)
}

type ExampleOnlyInstruction struct {
	Out string
	In  string
}

func (this *ExampleOnlyInstruction) Run(t *testing.T, es expreduceapi.EvalStateInterface, td TestDesc) bool {
	return true
}

type ResetState struct{}

func (this *ResetState) Run(t *testing.T, es expreduceapi.EvalStateInterface, td TestDesc) bool {
	es.ClearAll()
	return true
}

type TestComment struct {
	Comment string
}

func (this *TestComment) Run(t *testing.T, es expreduceapi.EvalStateInterface, td TestDesc) bool {
	return true
}

type SameTestEx struct {
	Out expreduceapi.Ex
	In  expreduceapi.Ex
}

func (this *SameTestEx) Run(t *testing.T, es expreduceapi.EvalStateInterface, td TestDesc) bool {
	succ, s := CasTestInner(es, es.Eval(this.In), es.Eval(this.Out), this.In.String(es), true, td.desc)
	assert.True(t, succ, s)
	return succ
}

func CasTestInner(es expreduceapi.EvalStateInterface, inTree expreduceapi.Ex, outTree expreduceapi.Ex, inStr string, test bool, desc string) (succ bool, s string) {
	theTestTree := atoms.NewExpression([]expreduceapi.Ex{
		atoms.NewSymbol("System`SameQ"),
		atoms.NewExpression([]expreduceapi.Ex{atoms.NewSymbol("System`Hold"), inTree}),
		atoms.NewExpression([]expreduceapi.Ex{atoms.NewSymbol("System`Hold"), outTree}),
	})

	theTest := es.Eval(theTestTree)

	context, ContextPath := DefinitionComplexityStringFormArgs()
	var buffer bytes.Buffer
	buffer.WriteString("(")
	buffer.WriteString(inTree.StringForm(expreduceapi.ToStringParams{Form: "InputForm", Context: context, ContextPath: ContextPath, Esi: es}))
	if test {
		buffer.WriteString(") != (")
	} else {
		buffer.WriteString(") == (")
	}
	buffer.WriteString(outTree.StringForm(expreduceapi.ToStringParams{Form: "InputForm", Context: context, ContextPath: ContextPath, Esi: es}))
	buffer.WriteString(")")
	buffer.WriteString("\n\tInput was: ")
	buffer.WriteString(inStr)
	if len(desc) != 0 {
		buffer.WriteString("\n\tDesc: ")
		buffer.WriteString(desc)
	}

	resSym, resIsSym := theTest.(*atoms.Symbol)
	if !resIsSym {
		return false, buffer.String()
	}
	if test {
		return resSym.Name == "System`True", buffer.String()
	}
	return resSym.Name == "System`False", buffer.String()
}

func CasAssertSame(t *testing.T, es expreduceapi.EvalStateInterface, out string, in string) bool {
	succ, s := CasTestInner(es, es.Eval(Interp(in, es)), es.Eval(Interp(out, es)), in, true, "")
	assert.True(t, succ, s)
	return succ
}

func CasAssertDiff(t *testing.T, es expreduceapi.EvalStateInterface, out string, in string) bool {
	succ, s := CasTestInner(es, es.Eval(Interp(in, es)), es.Eval(Interp(out, es)), in, false, "")
	assert.True(t, succ, s)
	return succ
}

func CasAssertDescSame(t *testing.T, es expreduceapi.EvalStateInterface, out string, in string, desc string) bool {
	succ, s := CasTestInner(es, es.Eval(Interp(in, es)), es.Eval(Interp(out, es)), in, true, desc)
	assert.True(t, succ, s)
	return succ
}
