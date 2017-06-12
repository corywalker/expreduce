package expreduce

type allocIterState struct {
	currForm int
	remaining int
	currFormI int
}

type allocIter struct {
	forms []parsedForm
	alloc []int
	stack []allocIterState
}

// Returns if should continue, result is stored in ai.alloc.
func (ai *allocIter) next() bool {
	for len(ai.stack) > 0 {
		var p allocIterState
		l := len(ai.stack)
		ai.stack, p = ai.stack[:l-1], ai.stack[l-1]
		if p.currForm-1 >= 0 {
			ai.alloc[p.currForm-1] = p.currFormI
		}
		if p.currForm >= len(ai.forms) {
			return true
		}
		// If we are on the last form, we can check directly if the last form
		// can accomodate the remaining components.
		if p.currForm+1 >= len(ai.forms) {
			if (ai.forms[p.currForm].startI <= p.remaining) && (p.remaining <= ai.forms[p.currForm].endI) {
				ai.stack = append(ai.stack, allocIterState{
				p.currForm+1, 0, p.remaining})
			}
		} else {
			for i := Min(ai.forms[p.currForm].endI, p.remaining); i >= ai.forms[p.currForm].startI; i-- {
				if p.remaining-i >= 0 {
					ai.stack = append(ai.stack, allocIterState{
					p.currForm+1, p.remaining-i, i})
				}
			}
		}
	}
	return false
}

func NewAllocIter(l int, forms []parsedForm) allocIter {
	ai := allocIter{}
	ai.forms = forms
	ai.alloc = make([]int, len(forms))
	ai.stack = []allocIterState{
		allocIterState{0, l, 0},
	}
	return ai
}
