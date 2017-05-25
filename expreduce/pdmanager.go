package expreduce

import (
	"bytes"
	"sort"
	"strings"
)

type PDManager struct {
	patternDefined map[string]Ex
}

func EmptyPD() *PDManager {
	return &PDManager{make(map[string]Ex)}
}

func CopyPD(orig *PDManager) (dest *PDManager) {
	dest = EmptyPD()
	// We do not care that this iterates in a random order.
	for k, v := range (*orig).patternDefined {
		(*dest).patternDefined[k] = v.DeepCopy()
	}
	return
}

func (this *PDManager) Update(toAdd *PDManager) {
	// We do not care that this iterates in a random order.
	for k, v := range (*toAdd).patternDefined {
		(*this).patternDefined[k] = v
	}
}

func (this *PDManager) String() string {
	var buffer bytes.Buffer
	buffer.WriteString("{")
	// We sort the keys here such that converting identical PDManagers always
	// produces the same string.
	keys := []string{}
	for k := range this.patternDefined {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	for _, k := range keys {
		v := this.patternDefined[k]
		buffer.WriteString(k)
		buffer.WriteString("_: ")
		buffer.WriteString(v.String())
		buffer.WriteString(", ")
	}
	if strings.HasSuffix(buffer.String(), ", ") {
		buffer.Truncate(buffer.Len() - 2)
	}
	buffer.WriteString("}")
	return buffer.String()
}

func (this *PDManager) Expression() Ex {
	res := NewExpression([]Ex{&Symbol{"List"}})
	// We sort the keys here such that converting identical PDManagers always
	// produces the same string.
	keys := []string{}
	for k := range this.patternDefined {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	for _, k := range keys {
		v := this.patternDefined[k]
		res.appendEx(NewExpression([]Ex{
			&Symbol{"Rule"},
			&String{k},
			v,
		}))
	}
	return res
}
