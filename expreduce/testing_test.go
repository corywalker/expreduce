package expreduce

import (
	"fmt"
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestTesting(t *testing.T) {
	fmt.Println("Testing testing")

	es := NewEvalState()

	CasAssertSame(t, es, " 1 ", "    1")
	succ, s := CasTestInner(es, es.Eval(Interp(" 1. ", es)), es.Eval(Interp("1  ", es)), " 1. ", true, "")
	assert.False(t, succ, s)
	CasAssertSame(t, es, "5.5", "1+1.5+3")
	CasAssertDiff(t, es, "5.6", "1+1.5+3")
	CasAssertSame(t, es, "9", "If[True, 9, 10]")
	CasAssertDiff(t, es, " 1. ", "    1")
}
