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
