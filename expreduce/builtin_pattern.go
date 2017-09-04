package expreduce

import "bytes"

func ToStringBlankType(repr string, parts []Ex, form string, context *String, contextPath *Expression) (bool, string) {
	if form == "FullForm" {
		return false, ""
	}
	if len(parts) == 1 {
		return true, repr
	} else if len(parts) == 2 {
		var buffer bytes.Buffer
		buffer.WriteString(repr)
		buffer.WriteString(parts[1].String())
		return true, buffer.String()
	}
	return false, ""
}

func GetPatternDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "MatchQ",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}

			if res, _ := IsMatchQ(this.Parts[1], this.Parts[2], EmptyPD(), es); res {
				return &Symbol{"System`True"}
			} else {
				return &Symbol{"System`False"}
			}
		},
	})
	defs = append(defs, Definition{
		Name: "Pattern",
		toString: func(this *Expression, form string, context *String, contextPath *Expression) (bool, string) {
			if len(this.Parts) != 3 {
				return false, ""
			}
			if form != "InputForm" && form != "OutputForm" {
				return false, ""
			}
			var buffer bytes.Buffer
			_, blankOk := HeadAssertion(this.Parts[2], "System`Blank")
			_, bsOk := HeadAssertion(this.Parts[2], "System`BlankSequence")
			_, bnsOk := HeadAssertion(this.Parts[2], "System`BlankNullSequence")
			if blankOk || bsOk || bnsOk {
				buffer.WriteString(this.Parts[1].StringForm(form, context, contextPath))
				buffer.WriteString(this.Parts[2].StringForm(form, context, contextPath))
			} else {
				buffer.WriteString("(")
				buffer.WriteString(this.Parts[1].StringForm(form, context, contextPath))
				buffer.WriteString(") : (")
				buffer.WriteString(this.Parts[2].StringForm(form, context, contextPath))
				buffer.WriteString(")")
			}
			return true, buffer.String()
		},
	})
	defs = append(defs, Definition{
		Name: "Blank",
		toString: func(this *Expression, form string, context *String, contextPath *Expression) (bool, string) {
			return ToStringBlankType("_", this.Parts, form, context, contextPath)
		},
	})
	defs = append(defs, Definition{
		Name: "BlankSequence",
		toString: func(this *Expression, form string, context *String, contextPath *Expression) (bool, string) {
			return ToStringBlankType("__", this.Parts, form, context, contextPath)
		},
	})
	defs = append(defs, Definition{
		Name: "BlankNullSequence",
		toString: func(this *Expression, form string, context *String, contextPath *Expression) (bool, string) {
			return ToStringBlankType("___", this.Parts, form, context, contextPath)
		},
	})
	defs = append(defs, Definition{
		Name: "Except",
	})
	defs = append(defs, Definition{
		Name: "PatternTest",
	})
	defs = append(defs, Definition{
		Name: "Condition",
	})
	defs = append(defs, Definition{
		Name: "Alternatives",
	})
	defs = append(defs, Definition{
		Name: "FreeQ",
	})
	defs = append(defs, Definition{
		Name: "ReplaceList",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}

			rule, isRule := HeadAssertion(this.Parts[2], "System`Rule")
			if !isRule {
				return this
			}
			res := NewExpression([]Ex{&Symbol{"System`List"}})
			mi, cont := NewMatchIter(this.Parts[1], rule.Parts[1], EmptyPD(), es)
			for cont {
				matchq, newPd, done := mi.next()
				cont = !done
				if matchq {
					res.appendEx(ReplacePD(rule.Parts[2], es, newPd))
				}
			}
			return res
		},
	})
	defs = append(defs, Definition{Name: "Repeated"})
	defs = append(defs, Definition{
		Name: "Optional",
		toString: func(this *Expression, form string, context *String, contextPath *Expression) (bool, string) {
			if len(this.Parts) != 2 {
				return false, ""
			}
			if form != "InputForm" && form != "OutputForm" {
				return false, ""
			}
			var buffer bytes.Buffer
			buffer.WriteString(this.Parts[1].StringForm(form, context, contextPath))
			buffer.WriteString(".")
			return true, buffer.String()
		},
	})
	defs = append(defs, Definition{
		Name: "Verbatim",
		// Not fully supported. Don't document
		OmitDocumentation: true,
	})
	defs = append(defs, Definition{Name: "HoldPattern"})
	return
}
