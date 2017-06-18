package expreduce

type parsedForm struct {
	startI		int
	endI		int
	form		Ex
	origForm	Ex
	isBlank		bool
	isImpliedBs	bool
	isOptional	bool
	formHasPattern	bool
	defaultExpr	Ex
}

func ParseRepeated(e *Expression) (Ex, int, int, bool) {
	min, max := -1, -1
	if len(e.Parts) < 2 {
		return nil, min, max, false
	}
	if len(e.Parts) >= 3 {
		list, isList := HeadAssertion(e.Parts[2], "List")
		if !isList {
			return nil, min, max, false
		}
		if len(list.Parts) != 2 {
			return nil, min, max, false
		}
		i, isInt := list.Parts[1].(*Integer)
		if !isInt {
			return nil, min, max, false
		}
		ival := i.Val.Int64()
		min = int(ival)
		max = min
	}
	return e.Parts[1], min, max, true
}

func ParseForm(lhs_component Ex, isFlat bool, sequenceHead string, headDefault Ex, cl *CASLogger) (res parsedForm) {
	// Calculate the min and max elements this component can match.
	pat, isPat := HeadAssertion(lhs_component, "Pattern")
	bns, isBns := HeadAssertion(lhs_component, "BlankNullSequence")
	bs, isBs := HeadAssertion(lhs_component, "BlankSequence")
	blank, isBlank := HeadAssertion(lhs_component, "Blank")
	repeated, isRepeated := HeadAssertion(lhs_component, "Repeated")
	repeatedNull, isRepeatedNull := HeadAssertion(lhs_component, "RepeatedNull")
	optional, isOptional := HeadAssertion(lhs_component, "Optional")
	if isPat {
		bns, isBns = HeadAssertion(pat.Parts[2], "BlankNullSequence")
		bs, isBs = HeadAssertion(pat.Parts[2], "BlankSequence")
		blank, isBlank = HeadAssertion(pat.Parts[2], "Blank")
		repeated, isRepeated = HeadAssertion(pat.Parts[2], "Repeated")
		repeatedNull, isRepeatedNull = HeadAssertion(pat.Parts[2], "RepeatedNull")
		optional, isOptional = HeadAssertion(pat.Parts[2], "Optional")
	}
	isImpliedBs := isBlank && isFlat
	// Ensure isBlank is exclusive from isImpliedBs
	isBlank = isBlank && !isImpliedBs

	form := lhs_component
	startI := 1 // also includes implied blanksequence
	endI := 1
	var defaultExpr Ex

	if isBns {
		form = BlankNullSequenceToBlank(bns)
		startI = 0
		endI = MaxInt
	} else if isImpliedBs {
		form = blank
		endI = MaxInt
		if len(blank.Parts) >= 2 {
			sym, isSym := blank.Parts[1].(*Symbol)
			if isSym {
				// If we have a pattern like k__Plus
				if sym.Name == sequenceHead {
					form = NewExpression([]Ex{&Symbol{"Blank"}})
					startI = 2
				} else {
					endI = 1
				}
			}
		}
	} else if isBlank {
		form = blank
	} else if isRepeated {
		repPat, repMin, repMax, repOk := ParseRepeated(repeated)
		if (repOk) {
			if repMin != -1 {
				startI = repMin
			}
			if repMax != -1 {
				endI = repMax
			} else {
				// an undefined end can match to the end of the sequence.
				endI = MaxInt
			}
			form = repPat
		}
	} else if isRepeatedNull {
		if len(repeatedNull.Parts) == 2 {
			startI = 0
			endI = MaxInt
			form = repeatedNull.Parts[1]
		}
	} else if isOptional {
		defaultToUse := headDefault
		if len(optional.Parts) >= 3 {
			defaultToUse = optional.Parts[2]
		}
		if len(optional.Parts) >= 2 {
			startI = 0
			if defaultToUse == nil {
				startI = 1
			}
			endI = 1
			form = optional.Parts[1]
			defaultExpr = defaultToUse
		}
	} else if isBs {
		form = BlankSequenceToBlank(bs)
		endI = MaxInt
	}
	cl.Debugf("Determined sequence startI = %v, endI = %v", startI, endI)

	res.startI = startI
	res.endI = endI
	res.form = form
	res.defaultExpr = defaultExpr
	res.origForm = lhs_component
	_, res.formHasPattern = HeadAssertion(form, "Pattern")
	res.isImpliedBs = isImpliedBs
	res.isOptional = isOptional
	res.isBlank = isBlank
	return res
}
