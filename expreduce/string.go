package expreduce

import "bytes"
import "github.com/cznic/wl"

type ToStringParams struct {
	form         string
	context      *String
	contextPath  *Expression
	previousHead string
	// Used by Definition[]
	es           *EvalState
}

func needsParens(thisHead string, previousHead string) bool {
	if previousHead == "<TOPLEVEL>" {
		return false
	}
	prevToken, prevTokenOk := headsToTokens[previousHead]
	thisToken, thisTokenOk := headsToTokens[thisHead]
	if prevTokenOk && thisTokenOk {
		prevPrec, prevPrecOk := wl.Precedence[prevToken]
		thisPrec, thisPrecOk := wl.Precedence[thisToken]
		if prevPrecOk && thisPrecOk {
			if prevPrec < thisPrec {
				return false
			}
		}
	}
	return true
}

func ToStringInfix(parts []Ex, delim string, thisHead string, p ToStringParams) (bool, string) {
	if p.form != "InputForm" && p.form != "OutputForm" && p.form != "TeXForm" {
		return false, ""
	}
	if len(parts) < 2 {
		return false, ""
	}
	addParens := needsParens(thisHead, p.previousHead)
	var buffer bytes.Buffer
	if addParens {
		if p.form == "TeXForm" {
			buffer.WriteString("{\\left(")
		} else {
			buffer.WriteString("(")
		}
	}
	nextParams := p
	nextParams.previousHead = thisHead
	for i := 0; i < len(parts); i++ {
		buffer.WriteString(parts[i].StringForm(nextParams))
		if i != len(parts)-1 {
			buffer.WriteString(delim)
		}
	}
	if addParens {
		if p.form == "TeXForm" {
			buffer.WriteString("\\right)}")
		} else {
			buffer.WriteString(")")
		}
	}
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
	return ToStringInfix(expr.Parts[1:], delim.Val, "", p)
}

// TODO(corywalker): Remove start, end. No users of these values.
func ToStringInfixAdvanced(parts []Ex, delim string, thisHead string, surroundEachArg bool, start string, end string, params ToStringParams) (bool, string) {
	if params.form != "InputForm" && params.form != "OutputForm" && params.form != "TeXForm" {
		return false, ""
	}
	if len(parts) < 2 {
		return false, ""
	}
	var buffer bytes.Buffer
	addParens := needsParens(thisHead, params.previousHead)
	if addParens {
		if params.form == "TeXForm" {
			buffer.WriteString("{\\left(")
		} else {
			buffer.WriteString("(")
		}
	}
	if !surroundEachArg {
		buffer.WriteString(start)
	}
	nextParams := params
	nextParams.previousHead = thisHead
	for i := 0; i < len(parts); i++ {
		if surroundEachArg {
			buffer.WriteString("(")
			buffer.WriteString(parts[i].StringForm(nextParams))
			buffer.WriteString(")")
		} else {
			buffer.WriteString(parts[i].StringForm(nextParams))
		}
		if i != len(parts)-1 {
			buffer.WriteString(delim)
		}
	}
	if !surroundEachArg {
		buffer.WriteString(end)
	}
	if addParens {
		if params.form == "TeXForm" {
			buffer.WriteString("\\right)}")
		} else {
			buffer.WriteString(")")
		}
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
		form:         form,
		context:      NewString(es.GetStringDef("System`$Context", "Global`")),
		contextPath:  es.GetListDef("System`$ContextPath"),
		previousHead: "<TOPLEVEL>",
		es: es,
	}

}

func simpleTeXToString(fnName string) func(*Expression, ToStringParams) (bool, string) {
	return (func(this *Expression, params ToStringParams) (bool, string) {
		if params.form != "TeXForm" {
			return false, ""
		}
		var buffer bytes.Buffer
		buffer.WriteString("\\" + fnName + " \\left(")
		for i := 1; i < len(this.Parts); i++ {
			buffer.WriteString(this.Parts[i].StringForm(params))
			if i != len(this.Parts)-1 {
				buffer.WriteString(",")
			}
		}
		buffer.WriteString("\\right)")
		return true, buffer.String()
	})
}
