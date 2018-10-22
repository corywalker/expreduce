package expreduce

import (
	"bytes"
	"testing"

	"github.com/corywalker/expreduce/expreduce/atoms"
	"github.com/corywalker/expreduce/expreduce/parser"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
	"github.com/stretchr/testify/assert"
)

type testDesc struct {
	module string
	def    Definition
	desc   string
}

type TestInstruction interface {
	run(t *testing.T, es expreduceapi.EvalStateInterface, td testDesc) bool
}

type SameTest struct {
	Out string
	In  string
}

func (this *SameTest) run(t *testing.T, es expreduceapi.EvalStateInterface, td testDesc) bool {
	return casAssertDescSame(t, es, this.Out, this.In, td.desc)
}

type StringTest struct {
	Out string
	In  string
}

func (this *StringTest) run(t *testing.T, es expreduceapi.EvalStateInterface, td testDesc) bool {
	return assert.Equal(t, this.Out, EasyRun(this.In, es), td.desc)
}

type ExampleOnlyInstruction struct {
	Out string
	In  string
}

func (this *ExampleOnlyInstruction) run(t *testing.T, es expreduceapi.EvalStateInterface, td testDesc) bool {
	return true
}

type ResetState struct{}

func (this *ResetState) run(t *testing.T, es expreduceapi.EvalStateInterface, td testDesc) bool {
	es.ClearAll()
	return true
}

type TestComment struct {
	Comment string
}

func (this *TestComment) run(t *testing.T, es expreduceapi.EvalStateInterface, td testDesc) bool {
	return true
}

type SameTestEx struct {
	Out expreduceapi.Ex
	In  expreduceapi.Ex
}

func (this *SameTestEx) run(t *testing.T, es expreduceapi.EvalStateInterface, td testDesc) bool {
	succ, s := casTestInner(es, es.Eval(this.In), es.Eval(this.Out), this.In.String(es), true, td.desc)
	assert.True(t, succ, s)
	return succ
}

func casTestInner(es expreduceapi.EvalStateInterface, inTree expreduceapi.Ex, outTree expreduceapi.Ex, inStr string, test bool, desc string) (succ bool, s string) {
	theTestTree := atoms.NewExpression([]expreduceapi.Ex{
		atoms.NewSymbol("System`SameQ"),
		atoms.NewExpression([]expreduceapi.Ex{atoms.NewSymbol("System`Hold"), inTree}),
		atoms.NewExpression([]expreduceapi.Ex{atoms.NewSymbol("System`Hold"), outTree}),
	})

	theTest := es.Eval(theTestTree)

	context, contextPath := definitionComplexityStringFormArgs()
	var buffer bytes.Buffer
	buffer.WriteString("(")
	buffer.WriteString(inTree.StringForm(expreduceapi.ToStringParams{Form: "InputForm", Context: context, ContextPath: contextPath, Esi: es}))
	if test {
		buffer.WriteString(") != (")
	} else {
		buffer.WriteString(") == (")
	}
	buffer.WriteString(outTree.StringForm(expreduceapi.ToStringParams{Form: "InputForm", Context: context, ContextPath: contextPath, Esi: es}))
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

func casAssertSame(t *testing.T, es expreduceapi.EvalStateInterface, out string, in string) bool {
	succ, s := casTestInner(es, es.Eval(parser.Interp(in, es)), es.Eval(parser.Interp(out, es)), in, true, "")
	assert.True(t, succ, s)
	return succ
}

func casAssertDiff(t *testing.T, es expreduceapi.EvalStateInterface, out string, in string) bool {
	succ, s := casTestInner(es, es.Eval(parser.Interp(in, es)), es.Eval(parser.Interp(out, es)), in, false, "")
	assert.True(t, succ, s)
	return succ
}

func casAssertDescSame(t *testing.T, es expreduceapi.EvalStateInterface, out string, in string, desc string) bool {
	succ, s := casTestInner(es, es.Eval(parser.Interp(in, es)), es.Eval(parser.Interp(out, es)), in, true, desc)
	assert.True(t, succ, s)
	return succ
}
