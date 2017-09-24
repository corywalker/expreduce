package expreduce

import "bytes"

type ToStringParams struct {
	form        string
	context     *String
	contextPath *Expression
}

func ToStringInfix(parts []Ex, delim string, p ToStringParams) (bool, string) {
	if p.form != "InputForm" && p.form != "OutputForm" {
		return false, ""
	}
	if len(parts) < 2 {
		return false, ""
	}
	var buffer bytes.Buffer
	buffer.WriteString("(")
	for i := 0; i < len(parts); i++ {
		buffer.WriteString(parts[i].StringForm(ToStringParams{p.form, p.context, p.contextPath}))
		if i != len(parts)-1 {
			buffer.WriteString(delim)
		}
	}
	buffer.WriteString(")")
	return true, buffer.String()
}

func (this *Expression) ToStringInfix(p ToStringParams) (bool, string) {
	if len(this.Parts) != 3 {
		return false, ""
	}
	expr, isExpr := this.Parts[1].(*Expression)
	delim, delimIsStr := this.Parts[2].(*String)
	if !isExpr || !delimIsStr {
		return false, ""
	}
	return ToStringInfix(expr.Parts[1:], delim.Val, p)
}

func ToStringInfixAdvanced(parts []Ex, delim string, surroundEachArg bool, start string, end string, params ToStringParams) (bool, string) {
	if params.form != "InputForm" && params.form != "OutputForm" {
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
			buffer.WriteString(parts[i].StringForm(params))
			buffer.WriteString(")")
		} else {
			buffer.WriteString(parts[i].StringForm(params))
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

func DefaultStringFormArgs() (*String, *Expression) {
	return NewString("Global`"), NewExpression([]Ex{
		NewSymbol("System`List"),
		NewString("System`"),
	})
}

func DefinitionComplexityStringFormArgs() (*String, *Expression) {
	// This was created because the "Private`" names in the blanks were
	// indicating greater complexity than they deserved.
	return NewString("Global`"), NewExpression([]Ex{
		NewSymbol("System`List"),
		NewString("System`"),
		NewString("Private`"),
	})
}

func ActualStringFormArgs(es *EvalState) (*String, *Expression) {
	return NewString(es.GetStringDef("System`$Context", "Global`")), es.GetListDef("System`$ContextPath")
}

func ActualStringFormArgsFull(form string, es *EvalState) ToStringParams {
	return ToStringParams{
		form,
		NewString(es.GetStringDef("System`$Context", "Global`")),
		es.GetListDef("System`$ContextPath"),
	}
}
