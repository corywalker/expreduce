package expreduce

import (
	"bytes"

	"github.com/corywalker/expreduce/expreduce/atoms"
	"github.com/corywalker/expreduce/expreduce/parser/parens"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

func toStringInfix(
	parts []expreduceapi.Ex,
	delim string,
	thisHead string,
	p expreduceapi.ToStringParams,
) (bool, string) {
	if p.Form != "InputForm" && p.Form != "OutputForm" && p.Form != "TeXForm" {
		return false, ""
	}
	if len(parts) < 2 {
		return false, ""
	}
	addParens := parens.NeedsParens(thisHead, p.PreviousHead)
	var buffer bytes.Buffer
	if addParens {
		if p.Form == "TeXForm" {
			buffer.WriteString("{\\left(")
		} else {
			buffer.WriteString("(")
		}
	}
	nextParams := p
	nextParams.PreviousHead = thisHead
	for i := 0; i < len(parts); i++ {
		buffer.WriteString(parts[i].StringForm(nextParams))
		if i != len(parts)-1 {
			buffer.WriteString(delim)
		}
	}
	if addParens {
		if p.Form == "TeXForm" {
			buffer.WriteString("\\right)}")
		} else {
			buffer.WriteString(")")
		}
	}
	return true, buffer.String()
}

func toStringInfixFn(
	this expreduceapi.ExpressionInterface,
	p expreduceapi.ToStringParams,
) (bool, string) {
	if len(this.GetParts()) != 3 {
		return false, ""
	}
	expr, isExpr := this.GetParts()[1].(expreduceapi.ExpressionInterface)
	delim, delimIsStr := this.GetParts()[2].(*atoms.String)
	if !isExpr || !delimIsStr {
		return false, ""
	}
	return toStringInfix(expr.GetParts()[1:], delim.Val, "", p)
}

// TODO(corywalker): Remove start, end. No users of these values.
func toStringInfixAdvanced(
	parts []expreduceapi.Ex,
	delim string,
	thisHead string,
	surroundEachArg bool,
	start string,
	end string,
	params expreduceapi.ToStringParams,
) (bool, string) {
	if params.Form != "InputForm" && params.Form != "OutputForm" &&
		params.Form != "TeXForm" {
		return false, ""
	}
	if len(parts) < 2 {
		return false, ""
	}
	var buffer bytes.Buffer
	addParens := parens.NeedsParens(thisHead, params.PreviousHead)
	if addParens {
		if params.Form == "TeXForm" {
			buffer.WriteString("{\\left(")
		} else {
			buffer.WriteString("(")
		}
	}
	if !surroundEachArg {
		buffer.WriteString(start)
	}
	nextParams := params
	for i := 0; i < len(parts); i++ {
		useTeXGrouping := false
		if thisHead == "System`Power" && params.Form == "TeXForm" && i == 1 {
			nextParams.PreviousHead = "<TOPLEVEL>"
			useTeXGrouping = true
		} else {
			nextParams.PreviousHead = thisHead
		}
		if useTeXGrouping {
			buffer.WriteString("{")
		}
		if surroundEachArg {
			buffer.WriteString("(")
			buffer.WriteString(parts[i].StringForm(nextParams))
			buffer.WriteString(")")
		} else {
			buffer.WriteString(parts[i].StringForm(nextParams))
		}
		if useTeXGrouping {
			buffer.WriteString("}")
		}
		if i != len(parts)-1 {
			buffer.WriteString(delim)
		}
	}
	if !surroundEachArg {
		buffer.WriteString(end)
	}
	if addParens {
		if params.Form == "TeXForm" {
			buffer.WriteString("\\right)}")
		} else {
			buffer.WriteString(")")
		}
	}
	return true, buffer.String()
}

func definitionComplexityStringFormArgs() (*atoms.String, expreduceapi.ExpressionInterface) {
	// This was created because the "Private`" names in the blanks were
	// indicating greater complexity than they deserved.
	return atoms.NewString("Global`"), atoms.NewExpression([]expreduceapi.Ex{
		atoms.NewSymbol("System`List"),
		atoms.NewString("System`"),
		atoms.NewString("Private`"),
	})

}

func actualStringFormArgs(
	es expreduceapi.EvalStateInterface,
) (*atoms.String, expreduceapi.ExpressionInterface) {
	return atoms.NewString(
			es.GetStringDef("System`$Context", "Global`"),
		), es.GetListDef(
			"System`$ContextPath",
		)
}

func ActualStringFormArgsFull(
	form string,
	es expreduceapi.EvalStateInterface,
) expreduceapi.ToStringParams {
	return expreduceapi.ToStringParams{
		Form: form,
		Context: atoms.NewString(
			es.GetStringDef("System`$Context", "Global`"),
		),
		ContextPath:  es.GetListDef("System`$ContextPath"),
		PreviousHead: "<TOPLEVEL>",
		Esi:          es,
	}

}

func simpleTeXToString(
	fnName string,
) func(expreduceapi.ExpressionInterface, expreduceapi.ToStringParams) (bool, string) {
	return (func(this expreduceapi.ExpressionInterface, params expreduceapi.ToStringParams) (bool, string) {
		if params.Form != "TeXForm" {
			return false, ""
		}
		var buffer bytes.Buffer
		buffer.WriteString("\\" + fnName + " \\left(")
		nextParams := params
		nextParams.PreviousHead = "<TOPLEVEL>"
		for i := 1; i < len(this.GetParts()); i++ {
			buffer.WriteString(this.GetParts()[i].StringForm(nextParams))
			if i != len(this.GetParts())-1 {
				buffer.WriteString(",")
			}
		}
		buffer.WriteString("\\right)")
		return true, buffer.String()
	})
}
