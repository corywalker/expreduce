package expreduce

import (
	"bytes"
	"github.com/stretchr/testify/assert"
	"testing"
)

type TestDesc struct {
	module string
	def    Definition
	desc   string
}

type TestInstruction interface {
	Run(t *testing.T, es *EvalState, td TestDesc)
}

type SameTest struct {
	Out string
	In  string
}

func (this *SameTest) Run(t *testing.T, es *EvalState, td TestDesc) {
	CasAssertSame(t, es, this.Out, this.In)
}

type DiffTest struct {
	Out string
	In  string
}

func (this *DiffTest) Run(t *testing.T, es *EvalState, td TestDesc) {
	CasAssertDiff(t, es, this.Out, this.In)
}

type StringTest struct {
	Out string
	In  string
}

func (this *StringTest) Run(t *testing.T, es *EvalState, td TestDesc) {
	assert.Equal(t, this.Out, EasyRun(this.In, es), td.desc)
}

type ExampleOnlyInstruction struct {
	Out string
	In  string
}

func (this *ExampleOnlyInstruction) Run(t *testing.T, es *EvalState, td TestDesc) {}

type ResetState struct{}

func (this *ResetState) Run(t *testing.T, es *EvalState, td TestDesc) {
	es.ClearAll()
}

type TestComment struct {
	Comment string
}

func (this *TestComment) Run(t *testing.T, es *EvalState, td TestDesc) {
}

func CasTestInner(es *EvalState, out string, in string, test bool) (succ bool, s string) {
	inTree := EvalInterp(in, es).Eval(es)
	outTree := EvalInterp(out, es).Eval(es)
	theTestTree := NewExpression([]Ex{
		&Symbol{"SameQ"},
		NewExpression([]Ex{&Symbol{"Hold"}, inTree}),
		NewExpression([]Ex{&Symbol{"Hold"}, outTree}),
	})

	theTest := theTestTree.Eval(es)

	var buffer bytes.Buffer
	buffer.WriteString("(")
	buffer.WriteString(inTree.String())
	if test {
		buffer.WriteString(") != (")
	} else {
		buffer.WriteString(") == (")
	}
	buffer.WriteString(outTree.String())
	buffer.WriteString(")")
	buffer.WriteString("\n\tInput was: ")
	buffer.WriteString(in)

	if test {
		return (theTest.String() == "True"), buffer.String()
	}
	return (theTest.String() == "False"), buffer.String()
}

func CasAssertSame(t *testing.T, es *EvalState, out string, in string) {
	succ, s := CasTestInner(es, out, in, true)
	assert.True(t, succ, s)
}

func CasAssertDiff(t *testing.T, es *EvalState, out string, in string) {
	succ, s := CasTestInner(es, out, in, false)
	assert.True(t, succ, s)
}
