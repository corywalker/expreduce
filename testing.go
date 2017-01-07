package cas

import (
	"bytes"
	"github.com/stretchr/testify/assert"
	"testing"
)

type TestInstruction interface {
	Run(t *testing.T, es *EvalState)
}

type SameTest struct {
	out string
	in  string
}

func (this *SameTest) Run(t *testing.T, es *EvalState) {
	CasAssertSame(t, es, this.out, this.in)
}

type DiffTest struct {
	out string
	in  string
}

func (this *DiffTest) Run(t *testing.T, es *EvalState) {
	CasAssertDiff(t, es, this.out, this.in)
}

type StringTest struct {
	out string
	in  string
}

func (this *StringTest) Run(t *testing.T, es *EvalState) {
	assert.Equal(t, this.out, EasyRun(this.in, es))
}

type ResetState struct{}

func (this *ResetState) Run(t *testing.T, es *EvalState) {
	es.ClearAll()
}

func CasTestInner(es *EvalState, out string, in string, test bool) (succ bool, s string) {
	inTree := EvalInterp(in, es).Eval(es)
	outTree := EvalInterp(out, es).Eval(es)
	theTestTree := &Expression{[]Ex{
		&Symbol{"SameQ"},
		&Expression{[]Ex{&Symbol{"Hold"}, inTree}},
		&Expression{[]Ex{&Symbol{"Hold"}, outTree}},
	}}
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
