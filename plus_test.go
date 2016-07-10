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
	assert.Equal(t, "-a - b", EasyRun("-1*(a + b)", es))
	assert.Equal(t, "-a - b", EasyRun("-(a + b)", es))
	assert.Equal(t, "((a + b) * -1.)", EasyRun("-1.*(a + b)", es))
	assert.Equal(t, "-a - b", EasyRun("(a + b)/-1", es))
	assert.Equal(t, "((a + b) * -1.)", EasyRun("(a + b)/-1.", es))

	es.ClearAll()
}
