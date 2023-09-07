// Package timecounter provides functionality for aggregating times based on a
// string key.
package timecounter

import (
	"bytes"
	"fmt"
	"sort"
)

type timeMap map[string]float64
type countMap map[string]int64

type timeCounter struct {
	times  timeMap
	counts countMap
}

func (tc *timeCounter) init() {
	tc.times = make(timeMap)
	tc.counts = make(countMap)
}

func (tc *timeCounter) addTime(key string, elapsed float64) {
	tc.times[key] += elapsed
	tc.counts[key]++
}

func (tc *timeCounter) update(other *timeCounter) {
	for k, v := range other.times {
		tc.addTime(k, v)
	}
}

func (tc *timeCounter) truncatedString(numToPrint int) string {
	var buffer bytes.Buffer
	n := map[float64][]string{}
	var a []float64
	for k, v := range tc.times {
		n[v] = append(n[v], k)
	}
	for k := range n {
		a = append(a, k)
	}
	sort.Sort(sort.Reverse(sort.Float64Slice(a)))
	numPrinted := 0
	for _, k := range a {
		if numPrinted >= numToPrint {
			break
		}
		for _, s := range n[k] {
			count := tc.counts[s]
			buffer.WriteString(fmt.Sprintf("%v, %v, %v\n", k, count, s))
			numPrinted++
		}
	}
	return buffer.String()
}

func (tc *timeCounter) string() string {
	return tc.truncatedString(25)
}

// Group

type counterGroupType uint8

const (
	// CounterGroupDefTime is the counter for definition times.
	CounterGroupDefTime counterGroupType = iota + 1
	// CounterGroupLHSDefTime is the counter for LHS definition times.
	CounterGroupLHSDefTime
	// CounterGroupEvalTime is the counter for eval times.
	CounterGroupEvalTime
	// CounterGroupHeadEvalTime is the counter for head eval times.
	CounterGroupHeadEvalTime
)

// Group collects eval-related timeCounters.
type Group struct {
	defTimeCounter      timeCounter
	lhsDefTimeCounter   timeCounter
	evalTimeCounter     timeCounter
	headEvalTimeCounter timeCounter
}

// Init initializes the Group with empty maps.
func (tcg *Group) Init() {
	tcg.defTimeCounter.init()
	tcg.lhsDefTimeCounter.init()
	tcg.evalTimeCounter.init()
	tcg.headEvalTimeCounter.init()
}

// AddTime adds a floating-point time to a particular timeCounter, selected with
// a counterGroupType.
func (tcg *Group) AddTime(
	counter counterGroupType,
	key string,
	elapsed float64,
) {
	if counter == CounterGroupDefTime {
		tcg.defTimeCounter.addTime(key, elapsed)
	} else if counter == CounterGroupLHSDefTime {
		tcg.lhsDefTimeCounter.addTime(key, elapsed)
	} else if counter == CounterGroupEvalTime {
		tcg.evalTimeCounter.addTime(key, elapsed)
	} else if counter == CounterGroupHeadEvalTime {
		tcg.headEvalTimeCounter.addTime(key, elapsed)
	}
}

// Update adds another Group to this one.
func (tcg *Group) Update(other *Group) {
	tcg.defTimeCounter.update(&other.defTimeCounter)
	tcg.lhsDefTimeCounter.update(&other.lhsDefTimeCounter)
	tcg.evalTimeCounter.update(&other.evalTimeCounter)
	tcg.headEvalTimeCounter.update(&other.headEvalTimeCounter)
}

// Prints the counter group as a formatted string.
func (tcg *Group) String() string {
	var buffer bytes.Buffer
	buffer.WriteString(tcg.defTimeCounter.string() + "\n")
	buffer.WriteString(tcg.lhsDefTimeCounter.string() + "\n")
	buffer.WriteString(tcg.evalTimeCounter.string() + "\n")
	buffer.WriteString(tcg.headEvalTimeCounter.string() + "\n")
	return buffer.String()
}
