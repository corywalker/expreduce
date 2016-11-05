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
	// More tests to be used in CommutativeIsMatchQ
	CasAssertSame(t, es, "False", "MemberQ[{a, b}, c]")
	CasAssertSame(t, es, "True", "MemberQ[{a, b}, a]")
	CasAssertSame(t, es, "True", "MemberQ[{a, b}, ___]")
	CasAssertSame(t, es, "True", "MemberQ[{a, b}, __]")
	CasAssertSame(t, es, "False", "MemberQ[{a, b}, __Integer]")
	CasAssertSame(t, es, "False", "MemberQ[{a, b}, ___Integer]")
	CasAssertSame(t, es, "True", "MemberQ[{a, b}, ___Symbol]")
	CasAssertSame(t, es, "True", "MemberQ[{a, b}, __Symbol]")
	CasAssertSame(t, es, "True", "MemberQ[{a, b, 1}, __Symbol]")
	CasAssertSame(t, es, "True", "MemberQ[{a, b, 1}, __Integer]")

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

	// Test Product
	CasAssertSame(t, es, "120", "Product[a, {a, 1, 5}]")
	CasAssertSame(t, es, "14400", "Product[a^2, {a, 1, 5}]")
	CasAssertSame(t, es, "576", "Product[a^2, {a, 4}]")

	// Test Map
	CasAssertSame(t, es, "{foo[a], foo[b], foo[c]}", "Map[foo, {a, b, c}]")
	CasAssertSame(t, es, "{foo[a], foo[b], foo[c]}", "foo /@ {a, b, c}")
	CasAssertSame(t, es, "{2, 4, 9}", "Times /@ {2, 4, 9}")
	CasAssertSame(t, es, "{foo[{a, b}], foo[c]}", "Map[foo, {{a, b}, c}]")
	CasAssertSame(t, es, "Map[foo]", "Map[foo]")
	CasAssertSame(t, es, "foo", "Map[foo, foo]")
	CasAssertSame(t, es, "Map[foo, foo, foo]", "Map[foo, foo, foo]")

	// Test Array
	CasAssertSame(t, es, "{f[1], f[2], f[3]}", "Array[f, 3]")
	CasAssertSame(t, es, "Null", "mytest[x_] := 5")
	CasAssertSame(t, es, "{5, 5, 5}", "Array[mytest, 3]")
	CasAssertSame(t, es, "{(a + b)[1], (a + b)[2], (a + b)[3]}", "Array[a + b, 3]")
	CasAssertSame(t, es, "Array[a, a]", "Array[a, a]")
	es.ClearAll()
}
