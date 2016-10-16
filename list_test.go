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

	// Test MemberQ
	es.ClearAll()
	CasAssertSame(t, es, "False", "MemberQ[{1, 2, 3}, 0]")
	CasAssertSame(t, es, "True", "MemberQ[{1, 2, 3}, 1]")
	CasAssertSame(t, es, "False", "MemberQ[{1, 2, 3}, {1}]")
	CasAssertSame(t, es, "True", "MemberQ[{1, 2, 3}, _Integer]")
	CasAssertSame(t, es, "True", "MemberQ[{1, 2, 3}, _]")
	CasAssertSame(t, es, "False", "MemberQ[{1, 2, 3}, _Real]")
	CasAssertSame(t, es, "True", "MemberQ[{1, 2, 3}, testmatch_Integer]")
	assert.Equal(t, "testmatch", EasyRun("testmatch", es))
	CasAssertSame(t, es, "{Protected}", "Attributes[MemberQ]")
	CasAssertSame(t, es, "False", "MemberQ[a, a]")
	CasAssertSame(t, es, "False", "MemberQ[a, _]")

	//CasAssertSame(t, es, "5000", "Length[Table[{3 + i + RandomReal[{-3, 7}], i + RandomReal[{-2, 5}]}, {i, 1, 5000}]]")

	// Test Sum
	es.ClearAll()
	CasAssertSame(t, es, "45", "Sum[i, {i, 5, 10}]")
	CasAssertSame(t, es, "55", "Sum[i, {i, 1, 10}]")
	CasAssertSame(t, es, "55", "Sum[i, {i, 0, 10}]")
	CasAssertSame(t, es, "450015000", "Sum[i, {i, 1, 30000}]")
	CasAssertSame(t, es, "450015000", "Sum[i, {i, 0, 30000}]")
	CasAssertSame(t, es, "1/2*n*(1 + n)", "Sum[i, {i, 0, n}]")
	CasAssertSame(t, es, "1/2*n*(1 + n)", "Sum[i, {i, 1, n}]")
}
