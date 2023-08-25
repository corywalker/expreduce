package expreduce

import (
	"fmt"
	"testing"

	"github.com/corywalker/expreduce/expreduce/parser"
	"github.com/stretchr/testify/assert"
)

func TestTesting(t *testing.T) {
	fmt.Println("Testing testing")

	es := NewEvalState()

	casAssertSame(t, es, " 1 ", "    1")
	succ, s := casTestInner(
		es,
		es.Eval(parser.Interp(" 1. ", es)),
		es.Eval(parser.Interp("1  ", es)),
		" 1. ",
		true,
		"",
		0,
	)
	assert.False(t, succ, s)
	casAssertSame(t, es, "5.5", "1+1.5+3")
	casAssertDiff(t, es, "5.6", "1+1.5+3")
	casAssertSame(t, es, "9", "If[True, 9, 10]")
	casAssertDiff(t, es, " 1. ", "    1")
}
