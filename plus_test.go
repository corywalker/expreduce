package cas

import (
	"fmt"
	"github.com/stretchr/testify/assert"
	"testing"
)

func TestPlus(t *testing.T) {

	fmt.Println("Testing plus")

	es := NewEvalState()

	// Test automatic expansion
	assert.Equal(t, "(a + b)", EasyRun("1*(a + b)", es))
	assert.Equal(t, "(1. * (a + b))", EasyRun("1.*(a + b)", es))
	assert.Equal(t, "(2. * (a + b))", EasyRun("2.*(a + b)", es))
	assert.Equal(t, "(a + b)", EasyRun("(a + b)/1", es))
	assert.Equal(t, "((a + b) * 1.)", EasyRun("(a + b)/1.", es))
	assert.Equal(t, "(2 * (a + b))", EasyRun("2*(a + b)", es))
	assert.Equal(t, "(a * (b + c))", EasyRun("a*(b + c)", es))
	assert.Equal(t, "((a * -1) + (b * -1))", EasyRun("-1*(a + b)", es))
	assert.Equal(t, "((a * -1) + (b * -1))", EasyRun("-(a + b)", es))
	assert.Equal(t, "((a + b) * -1.)", EasyRun("-1.*(a + b)", es))
	assert.Equal(t, "((a * -1) + (b * -1))", EasyRun("(a + b)/-1", es))
	assert.Equal(t, "((a + b) * -1.)", EasyRun("(a + b)/-1.", es))

	// Test that we do not delete all the addends
	CasAssertSame(t, es, "0.", "(5.2 - .2) - 5")
	CasAssertSame(t, es, "0", "0 + 0")

	es.ClearAll()
}
