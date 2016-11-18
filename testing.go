package cas

import (
	"bytes"
	"github.com/stretchr/testify/assert"
	"testing"
)

func CasTestInner(es *EvalState, out string, in string, test bool) (succ bool, s string) {
	inTree := EvalInterp(in, es)
	outTree := EvalInterp(out, es)
	theTestTree := &Expression{[]Ex{&Symbol{"SameQ"}, inTree, outTree}}
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
