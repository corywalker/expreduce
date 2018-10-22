package matcher

import (
	"fmt"
	"testing"

	"github.com/stretchr/testify/assert"
)

func newPf(startI int, endI int) parsedForm {
	return parsedForm{
		startI, endI,
		nil, nil,
		false, false, false, nil, false, nil,
	}
}

// sequenceAssignments[len_Integer, forms_List, orderless_?BooleanQ] :=
//  ReplaceList[
//   fn @@ Range[0, len - 1] /.
//    fn -> If[orderless, ExpreduceOrderlessFn, foo],
//   fn @@ Table[
//       Pattern[Alphabet[][[i]] // ToExpression // Evaluate,
//        Repeated[_, forms[[i]]]], {i, Length[forms]}] ->
//     Table[{Alphabet[][[i]] // ToExpression}, {i, Length[forms]}] /.
//    fn -> If[orderless, ExpreduceOrderlessFn, foo]]

func TestAllocations(t *testing.T) {
	fmt.Println("Testing allocations")

	forms := []parsedForm{
		newPf(1, 2),
		newPf(0, 1),
		newPf(0, 99999),
	}
	ai := NewAllocIter(4, forms)
	assert.Equal(t, true, ai.next())
	assert.Equal(t, []int{1, 0, 3}, ai.alloc)
	assert.Equal(t, true, ai.next())
	assert.Equal(t, []int{1, 1, 2}, ai.alloc)
	assert.Equal(t, true, ai.next())
	assert.Equal(t, []int{2, 0, 2}, ai.alloc)
	assert.Equal(t, true, ai.next())
	assert.Equal(t, []int{2, 1, 1}, ai.alloc)
	assert.Equal(t, false, ai.next())

	forms = []parsedForm{
		newPf(1, 1),
		newPf(0, 99999),
	}
	ai = NewAllocIter(4, forms)
	assert.Equal(t, true, ai.next())
	assert.Equal(t, []int{1, 3}, ai.alloc)
	assert.Equal(t, false, ai.next())

	forms = []parsedForm{
		newPf(1, 1),
		newPf(1, 1),
		newPf(0, 99999),
	}
	ai = NewAllocIter(4, forms)
	assert.Equal(t, true, ai.next())
	assert.Equal(t, []int{1, 1, 2}, ai.alloc)
	assert.Equal(t, false, ai.next())

	forms = []parsedForm{
		newPf(0, 1),
		newPf(0, 1),
		newPf(0, 99999),
	}
	forms[0].isOptional = true
	forms[1].isOptional = true
	ai = NewAllocIter(3, forms)
	assert.Equal(t, true, ai.next())
	assert.Equal(t, []int{1, 1, 1}, ai.alloc)
	assert.Equal(t, true, ai.next())
	assert.Equal(t, []int{1, 0, 2}, ai.alloc)
	assert.Equal(t, true, ai.next())
	assert.Equal(t, []int{0, 1, 2}, ai.alloc)
	assert.Equal(t, true, ai.next())
	assert.Equal(t, []int{0, 0, 3}, ai.alloc)
	assert.Equal(t, false, ai.next())

	forms = []parsedForm{
		newPf(0, 99999),
		newPf(1, 1),
		newPf(0, 99999),
	}
	ai = NewAllocIter(4, forms)
	assert.Equal(t, true, ai.next())
	assert.Equal(t, []int{0, 1, 3}, ai.alloc)
	assert.Equal(t, true, ai.next())
	assert.Equal(t, []int{1, 1, 2}, ai.alloc)
	assert.Equal(t, true, ai.next())
	assert.Equal(t, []int{2, 1, 1}, ai.alloc)
	assert.Equal(t, true, ai.next())
	assert.Equal(t, []int{3, 1, 0}, ai.alloc)
	assert.Equal(t, false, ai.next())

	forms = []parsedForm{
		newPf(0, 99999),
	}
	ai = NewAllocIter(0, forms)
	assert.Equal(t, true, ai.next())
	assert.Equal(t, []int{0}, ai.alloc)
	assert.Equal(t, false, ai.next())

	forms = []parsedForm{
		newPf(1, 99999),
	}
	ai = NewAllocIter(0, forms)
	assert.Equal(t, false, ai.next())

	// Impossible configuration. Should return false immediately.
	forms = []parsedForm{
		newPf(5, 5),
	}
	ai = NewAllocIter(4, forms)
	assert.Equal(t, false, ai.next())

	// Impossible configuration. Should return false immediately.
	forms = []parsedForm{
		newPf(1, 1),
	}
	ai = NewAllocIter(4, forms)
	assert.Equal(t, false, ai.next())

	// Impossible configuration. Should return false immediately.
	forms = []parsedForm{
		newPf(5, 0),
	}
	ai = NewAllocIter(4, forms)
	assert.Equal(t, false, ai.next())

	forms = []parsedForm{
		newPf(0, 999999),
		newPf(1, 1),
		newPf(0, 999999),
	}
	ai = NewAllocIter(800000, forms)
	num := 0
	for num = 0; ai.next(); num++ {
	}
	assert.Equal(t, 800000, num)

	// should be 1/2 n (1+n)/.n->(ncomps-1)
	forms = []parsedForm{
		newPf(0, 999999),
		newPf(1, 1),
		newPf(0, 999999),
		newPf(1, 1),
		newPf(0, 999999),
	}
	ai = NewAllocIter(1400, forms)
	for num = 0; ai.next(); num++ {
	}
	assert.Equal(t, 979300, num)
}

func allMatch(nComps int, nForms int) [][]bool {
	formMatches := make([][]bool, nForms)
	for i := 0; i < nForms; i++ {
		formMatches[i] = make([]bool, nComps)
		for j := 0; j < nComps; j++ {
			formMatches[i][j] = true
		}
	}
	return formMatches
}

func TestAssignments(t *testing.T) {
	fmt.Println("Testing assignments")

	forms := []parsedForm{
		newPf(0, 1),
		newPf(1, 1),
		newPf(0, 99999),
	}
	nComps := 3
	ai := NewAssnIter(nComps, forms, allMatch(nComps, len(forms)), true)
	assert.Equal(t, true, ai.next())
	assert.Equal(t, [][]int{{}, {0}, {1, 2}}, ai.assns)
	assert.Equal(t, true, ai.next())
	assert.Equal(t, [][]int{{}, {1}, {0, 2}}, ai.assns)
	assert.Equal(t, true, ai.next())
	assert.Equal(t, [][]int{{}, {2}, {0, 1}}, ai.assns)
	assert.Equal(t, true, ai.next())
	assert.Equal(t, [][]int{{0}, {1}, {2}}, ai.assns)
	assert.Equal(t, true, ai.next())
	assert.Equal(t, [][]int{{0}, {2}, {1}}, ai.assns)
	assert.Equal(t, true, ai.next())
	assert.Equal(t, [][]int{{1}, {0}, {2}}, ai.assns)
	assert.Equal(t, true, ai.next())
	assert.Equal(t, [][]int{{1}, {2}, {0}}, ai.assns)
	assert.Equal(t, true, ai.next())
	assert.Equal(t, [][]int{{2}, {0}, {1}}, ai.assns)
	assert.Equal(t, true, ai.next())
	assert.Equal(t, [][]int{{2}, {1}, {0}}, ai.assns)
	assert.Equal(t, false, ai.next())

	ai = NewAssnIter(nComps, forms, allMatch(nComps, len(forms)), false)
	assert.Equal(t, true, ai.next())
	assert.Equal(t, [][]int{{}, {0}, {1, 2}}, ai.assns)
	assert.Equal(t, true, ai.next())
	assert.Equal(t, [][]int{{0}, {1}, {2}}, ai.assns)
	assert.Equal(t, false, ai.next())

	// Test pinning a form to particular components.
	forms = []parsedForm{
		newPf(1, 1),
		newPf(1, 1),
		newPf(1, 1),
	}
	nComps = 3
	formMatches := [][]bool{
		{true, true, true},
		{false, true, false},
		{true, true, true},
	}
	ai = NewAssnIter(nComps, forms, formMatches, true)
	assert.Equal(t, true, ai.next())
	assert.Equal(t, [][]int{{0}, {1}, {2}}, ai.assns)
	assert.Equal(t, true, ai.next())
	assert.Equal(t, [][]int{{2}, {1}, {0}}, ai.assns)
	assert.Equal(t, false, ai.next())

	forms = []parsedForm{
		newPf(1, 99999),
		newPf(1, 99999),
	}
	nComps = 3
	formMatches = [][]bool{
		{true, true, true},
		{true, false, false},
	}
	ai = NewAssnIter(nComps, forms, formMatches, true)
	assert.Equal(t, true, ai.next())
	assert.Equal(t, [][]int{{1, 2}, {0}}, ai.assns)
	assert.Equal(t, false, ai.next())

	// should be 1/2 n (1+n)/.n->(ncomps-1)
	forms = []parsedForm{
		newPf(0, 999999),
		newPf(1, 1),
		newPf(0, 999999),
		newPf(1, 1),
		newPf(0, 999999),
	}
	nComps = 1400
	ai = NewAssnIter(nComps, forms, allMatch(nComps, len(forms)), false)
	num := 0
	for num = 0; ai.next(); num++ {
	}
	assert.Equal(t, 979300, num)

	nComps = 8
	ai = NewAssnIter(nComps, forms, allMatch(nComps, len(forms)), true)
	for num = 0; ai.next(); num++ {
	}
	assert.Equal(t, 40824, num)
}
