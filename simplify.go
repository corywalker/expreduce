package cas

func (this *Expression) RepeatRun(es *EvalState, rule string) {
	this.Parts[1] = (&Expression{[]Ex{&Symbol{"ReplaceRepeated"}, this.Parts[1], Interp(rule)}}).Eval(es)
}

func (this *Expression) EvalBasicSimplify(es *EvalState) Ex {
	if len(this.Parts) != 2 {
		return this
	}

	// Simplify expressions with Infinity
	this.RepeatRun(es, "Infinity + matcha_Integer -> Infinity")
	this.RepeatRun(es, "Infinity + matcha_Real -> Infinity")
	this.RepeatRun(es, "-Infinity + matcha_Integer -> -Infinity")
	this.RepeatRun(es, "-Infinity + matcha_Real -> -Infinity")
	this.RepeatRun(es, "Infinity - Infinity -> Indeterminate")
	this.RepeatRun(es, "1/Infinity -> 0")

	this.RepeatRun(es, "amatch_ - amatch_ -> 0")
	this.RepeatRun(es, "(c1match_Integer*matcha_) + (c2match_Integer*matcha_) -> (c1match+c2match)*matcha")
	this.RepeatRun(es, "(c1match_Integer*matcha_) + matcha_ -> (c1match+1)*matcha")
	this.RepeatRun(es, "matcha_ + matcha_ -> 2*matcha")
	this.RepeatRun(es, "(c1match_Integer*matcha_) + matcha_ -> (c1match+1)*matcha")
	this.RepeatRun(es, "(c1match_Real*matcha_) + (c2match_Integer*matcha_) -> (c1match+c2match)*matcha")

	this.RepeatRun(es, "0*matcha_ -> 0")
	this.RepeatRun(es, "matcha_/matcha_ -> 1")
	this.RepeatRun(es, "matcha_*matcha_ -> matcha^2")
	this.RepeatRun(es, "matcha_^matchb_ / matcha_ -> matcha^(matchb-1)")
	this.RepeatRun(es, "matcha_^matchb_ / matcha_^matchc_ -> matcha^(matchb-matchc)")
	this.RepeatRun(es, "matcha_^matchb_ * matcha_ -> matcha^(matchb+1)")
	this.RepeatRun(es, "matcha_^matchb_ * matcha_^matchc_ -> matcha^(matchb+matchc)")

	// Simplify nested exponents
	this.RepeatRun(es, "(matcha_^matchb_Integer)^matchc_Integer -> matcha^(matchb^matchc)")
	this.RepeatRun(es, "(matcha_^matchb_Real)^matchc_Integer -> matcha^(matchb^matchc)")

	return this.Parts[1]
}
