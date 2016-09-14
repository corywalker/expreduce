package cas

import (
	"bytes"
	"github.com/stretchr/testify/assert"
	"testing"
)

func CasTestInner(es *EvalState, out string, in string, test bool) (succ bool, s string) {
	inTree := (&BasicSimplify{EvalInterp(in, es)}).Eval(es)
	outTree := Interp(out)
	theTestTree := SameQ{Lhs: inTree, Rhs: outTree}
	theTest := theTestTree.Eval(es)

	var buffer bytes.Buffer
	buffer.WriteString("(")
	buffer.WriteString(inTree.ToString())
	if test {
		buffer.WriteString(") != (")
	} else {
		buffer.WriteString(") == (")
	}
	buffer.WriteString(outTree.ToString())
	buffer.WriteString(")")
	buffer.WriteString("\n\tInput was: ")
	buffer.WriteString(in)

	if test {
		return (theTest.ToString() == "True"), buffer.String()
	}
	return (theTest.ToString() == "False"), buffer.String()
}

func CasAssertSame(t *testing.T, es *EvalState, out string, in string) {
	succ, s := CasTestInner(es, out, in, true)
	assert.True(t, succ, s)
}

func CasAssertDiff(t *testing.T, es *EvalState, out string, in string) {
	succ, s := CasTestInner(es, out, in, false)
	assert.True(t, succ, s)
}
