package cas

import "bytes"

func (this *Expression) ToStringList() string {
	var buffer bytes.Buffer
	buffer.WriteString("{")
	for i, e := range this.Parts[1:] {
		buffer.WriteString(e.ToString())
		if i != len(this.Parts[1:])-1 {
			buffer.WriteString(", ")
		}
	}
	buffer.WriteString("}")
	return buffer.String()
}
