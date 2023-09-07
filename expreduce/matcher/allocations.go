package matcher

func min(x, y int) int {
	if x < y {
		return x
	}
	return y
}

type allocIterState struct {
	currForm  int
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
			if (ai.forms[p.currForm].startI <= p.remaining) &&
				(p.remaining <= ai.forms[p.currForm].endI) {
				ai.stack = append(ai.stack, allocIterState{
					p.currForm + 1, 0, p.remaining})
			}
		} else {
			// Optional forms fill eagerly instead of lazily.
			// TODO: clean up this code and determine if we ever need to handle
			// an optional form without a startI == 0 and endI == 1.
			if ai.forms[p.currForm].isOptional {
				for i := ai.forms[p.currForm].startI; i <= min(ai.forms[p.currForm].endI, p.remaining); i++ {
					if p.remaining-i >= 0 {
						ai.stack = append(ai.stack, allocIterState{
							p.currForm + 1, p.remaining - i, i})
					}
				}
			} else {
				for i := min(ai.forms[p.currForm].endI, p.remaining); i >= ai.forms[p.currForm].startI; i-- {
					if p.remaining-i >= 0 {
						ai.stack = append(ai.stack, allocIterState{
							p.currForm + 1, p.remaining - i, i})
					}
				}
			}
		}
	}
	return false
}

func newAllocIter(l int, forms []parsedForm) allocIter {
	ai := allocIter{}
	ai.forms = forms
	ai.alloc = make([]int, len(forms))
	ai.stack = []allocIterState{
		{0, l, 0},
	}
	return ai
}

type assnIterState struct {
	lastTaken int
	// For example, if we have the orderless sequence {a, b}, and we are trying
	// to do all asignments of it to two BlankNullSequences, we have an
	// underlying data structure called assnData which could contain {0, 1} or
	// {1, 0} in the case where the assignment was {{1}, {0}}.
	assnDataI       int
	crossedBoundary bool
	toFree          int
}

type assnIter struct {
	forms              []parsedForm
	assnData           []int
	assnIndices        []int
	assns              [][]int
	formMatches        [][]bool
	orderless          bool
	taken              []bool
	stack              []assnIterState
	iteratingOrderless bool
	ai                 allocIter
}

func (asi *assnIter) nextOrderless() bool {
	for len(asi.stack) > 0 {
		var p assnIterState
		l := len(asi.stack)
		asi.stack, p = asi.stack[:l-1], asi.stack[l-1]

		if p.toFree > -1 {
			asi.taken[p.toFree] = false
			continue
		}
		if p.assnDataI > 0 {
			asi.taken[p.lastTaken] = true
			asi.assnData[p.assnDataI-1] = p.lastTaken
		}
		if p.assnDataI >= len(asi.assnData) {
			if p.assnDataI > 0 {
				asi.stack = append(asi.stack, assnIterState{
					-1, 0, true, p.lastTaken,
				})
			}
			return true
		}
		// Determine if we crossed an allocation boundary.
		formI := asi.assnIndices[p.assnDataI]
		willCrossBoundary := false
		if p.assnDataI+1 < len(asi.assnIndices) {
			willCrossBoundary = formI != asi.assnIndices[p.assnDataI+1]
		}

		startI := p.lastTaken + 1
		if p.crossedBoundary {
			startI = 0
		}
		if p.assnDataI > 0 {
			asi.stack = append(asi.stack, assnIterState{
				-1, 0, true, p.lastTaken,
			})
		}
		for i := len(asi.taken) - 1; i >= startI; i-- {
			if !asi.taken[i] && asi.formMatches[formI][i] {
				asi.stack = append(asi.stack, assnIterState{
					i, p.assnDataI + 1, willCrossBoundary, -1,
				})
			}
		}
	}
	return false
}

func (asi *assnIter) next() bool {
	if asi.iteratingOrderless && asi.nextOrderless() {
		return true
	}
	asi.iteratingOrderless = false
	for asi.ai.next() {
		// Create slices against assnData.
		// TODO: non-orderless needs to support formMatches as well.
		// ReplaceList[ExpreduceFlatFn[a,b,c],ExpreduceFlatFn[x___//pm,b//pm,y___//pm]->{{x},{y}}]
		lasti := 0
		for i := range asi.assns {
			asi.assns[i] = asi.assnData[lasti : lasti+asi.ai.alloc[i]]
			for j := lasti; j < lasti+asi.ai.alloc[i]; j++ {
				asi.assnIndices[j] = i
			}
			lasti += asi.ai.alloc[i]
		}
		if asi.orderless {
			asi.stack = append(asi.stack, assnIterState{
				-1, 0, true, -1,
			})
			if !asi.nextOrderless() {
				// I used to not have this, but this can trigger now that we
				// have formMatches. Now, MatchQ[ExpreduceOrderlessFn[a,b],ExpreduceOrderlessFn[b,b]]
				// can actually fail before creating any orderless assignments.
				continue
			}
			asi.iteratingOrderless = true
		}
		return true
	}
	return false
}

func newAssnIter(
	l int,
	forms []parsedForm,
	formMatches [][]bool,
	orderless bool,
) assnIter {
	asi := assnIter{}
	asi.forms = forms
	asi.assnData = make([]int, l)
	asi.assnIndices = make([]int, l)
	asi.assns = make([][]int, len(forms))
	asi.orderless = orderless
	asi.taken = make([]bool, l)
	asi.formMatches = formMatches

	asi.ai = newAllocIter(len(asi.assnData), asi.forms)
	for i := range asi.assnData {
		asi.assnData[i] = i
	}

	return asi
}
