package expreduce

import "bytes"

func ToStringInfix(parts []Ex, delim string, form string) (bool, string) {
	if form != "InputForm" && form != "OutputForm" {
		return false, ""
	}
	if len(parts) < 2 {
		return false, ""
	}
	var buffer bytes.Buffer
	buffer.WriteString("(")
	for i := 0; i < len(parts); i++ {
		buffer.WriteString(parts[i].StringForm(form))
		if i != len(parts)-1 {
			buffer.WriteString(delim)
		}
	}
	buffer.WriteString(")")
	return true, buffer.String()
}

func (this *Expression) ToStringInfix(form string) (bool, string) {
	if len(this.Parts) != 3 {
		return false, ""
	}
	expr, isExpr := this.Parts[1].(*Expression)
	delim, delimIsStr := this.Parts[2].(*String)
	if !isExpr || !delimIsStr {
		return false, ""
	}
	return ToStringInfix(expr.Parts[1:], delim.Val, form)
}

func ToStringInfixAdvanced(parts []Ex, delim string, surroundEachArg bool, start string, end string, form string) (bool, string) {
	if form != "InputForm" && form != "OutputForm" {
		return false, ""
	}
	if len(parts) < 2 {
		return false, ""
	}
	var buffer bytes.Buffer
	if !surroundEachArg {
		buffer.WriteString(start)
	}
	for i := 0; i < len(parts); i++ {
		if surroundEachArg {
			buffer.WriteString("(")
			buffer.WriteString(parts[i].String())
			buffer.WriteString(")")
		} else {
			buffer.WriteString(parts[i].String())
		}
		if i != len(parts)-1 {
			buffer.WriteString(delim)
		}
	}
	if !surroundEachArg {
		buffer.WriteString(end)
	}
	return true, buffer.String()
}

func (this *String) NeedsEval() bool {
	return false
}
