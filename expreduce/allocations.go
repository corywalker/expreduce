package expreduce

import "fmt"

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

type assnIterState struct {
	lastTaken int
	formDataI int
	crossedBoundary bool
	toFree int
}

type assnIter struct {
	forms []parsedForm
	assnData []int
	assns [][]int
	orderless bool
	taken []bool
	stack []assnIterState
}

func (asi *assnIter) pOrderless() bool {
	for len(asi.stack) > 0 {
		var p assnIterState
		l := len(asi.stack)
		asi.stack, p = asi.stack[:l-1], asi.stack[l-1]
		lastTaken, formDataI, crossedBoundary, toFree := p.lastTaken, p.formDataI, p.crossedBoundary, p.toFree

		if toFree > -1 {
			asi.taken[toFree] = false
			continue
		}
		if formDataI > 0 {
			asi.taken[lastTaken] = true
			asi.assnData[formDataI-1] = lastTaken
		}
		if formDataI >= len(asi.assnData) {
			if formDataI > 0 {
				asi.stack = append(asi.stack, assnIterState{
					-1, 0, true, lastTaken,
				})
			}
			return true
		}
		// Determine if we crossed an allocation boundary.
		totComps := 0
		for i := 0; i < len(asi.assns) && totComps < formDataI+1; i++ {
			totComps += len(asi.assns[i])
		}
		willCrossBoundary := formDataI+1 == totComps

		startI := lastTaken+1
		if crossedBoundary {
			startI = 0
		}
		if formDataI > 0 {
			asi.stack = append(asi.stack, assnIterState{
				-1, 0, true, lastTaken,
			})
		}
		for i := len(asi.taken)-1; i >= startI; i-- {
			if !asi.taken[i] {
				asi.stack = append(asi.stack, assnIterState{
					i, formDataI+1, willCrossBoundary, -1,
				})
			}
		}
	}
	return false
}

func (asi *assnIter) p() {
	ai := NewAllocIter(len(asi.assnData), asi.forms)
	for i := range asi.assnData {
		asi.assnData[i] = i
	}
	for ai.next() {
		// Create slices against assnData.
		lasti := 0
		for i := range asi.assns {
			asi.assns[i] = asi.assnData[lasti:lasti+ai.alloc[i]]
			lasti += ai.alloc[i]
		}
		if !asi.orderless {
			fmt.Println(ai.alloc)
			fmt.Println(asi.assns)
		} else {
			asi.stack = append(asi.stack, assnIterState{
				-1, 0, true, -1,
			})
			for asi.pOrderless() {
				fmt.Println(asi.assns)
			}
		}
	}
}

func NewAssnIter(l int, forms []parsedForm, orderless bool) assnIter {
	asi := assnIter{}
	asi.forms = forms
	asi.assnData = make([]int, l)
	asi.assns = make([][]int, len(forms))
	asi.orderless = orderless
	asi.taken = make([]bool, l)
	return asi
}
