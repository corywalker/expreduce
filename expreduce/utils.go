package expreduce

import (
	"bytes"
)

func ExArrayToString(exArray []Ex) string {
	var buffer bytes.Buffer
	buffer.WriteString("{")
	for i, e := range exArray {
		buffer.WriteString(e.String())
		if i != len(exArray)-1 {
			buffer.WriteString(", ")
		}
	}
	buffer.WriteString("}")
	return buffer.String()
}

func PFArrayToString(pfArray []parsedForm) string {
	var buffer bytes.Buffer
	buffer.WriteString("{")
	for i, e := range pfArray {
		buffer.WriteString(e.origForm.String())
		if i != len(pfArray)-1 {
			buffer.WriteString(", ")
		}
	}
	buffer.WriteString("}")
	return buffer.String()
}

func ExArrayDeepCopy(exArray []Ex) []Ex {
	res := make([]Ex, len(exArray))
	for i, e := range exArray {
		res[i] = e.DeepCopy()
	}
	return res
}

func Max(x, y int) int {
	if x > y {
		return x
	}
	return y
}

func Min(x, y int) int {
	if x < y {
		return x
	}
	return y
}
