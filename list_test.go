package cas

import (
	"fmt"
	"github.com/stretchr/testify/assert"
	"testing"
)

func TestList(t *testing.T) {

	fmt.Println("Testing list")

	es := NewEvalState()

	CasAssertSame(t, es, "10", "Total[{1,2,3,4}]")
	// Use full List expression because the interpreter cannot currently
	// parse "{}"
	CasAssertSame(t, es, "0", "Total[List[]]")
	CasAssertSame(t, es, "4", "Length[{1,2,3,4}]")
	CasAssertSame(t, es, "0", "Length[List[]]")
	CasAssertSame(t, es, "1", "Length[{5}]")
	CasAssertSame(t, es, "11/2", "Mean[{5,6}]")

	es.ClearAll()
	CasAssertSame(t, es, "{a, a, a, a, a}", "Table[a, 5]")
	CasAssertSame(t, es, "{5, 6, 7, 8, 9, 10}", "Table[i, {i, 5, 10}]")
	assert.Equal(t, "i", EasyRun("i", es))
	CasAssertSame(t, es, "10", "i = 10")
	CasAssertSame(t, es, "{5, 6, 7, 8, 9, 10}", "Table[i, {i, 5, 10}]")
	assert.Equal(t, "10", EasyRun("i", es))
	CasAssertSame(t, es, "{1, 4, 9, 16, 25, 36, 49, 64, 81, 100}", "Table[n^2, {n, 1, 10}]")
}
