package cas

import "bytes"

type BasicSimplify struct {
	Expr Ex
}

func (this *BasicSimplify) RepeatRun(es *EvalState, rule string) {
	this.Expr = (&ReplaceRepeated{this.Expr, Interp(rule)}).Eval(es)
}

func (this *BasicSimplify) Eval(es *EvalState) Ex {
	this.RepeatRun(es, "amatch_ - amatch_ -> 0")
	this.RepeatRun(es, "(c1match_Integer*matcha_) + (c2match_Integer*matcha_) -> (c1match+c2match)*matcha")
	this.RepeatRun(es, "(c1match_Integer*matcha_) + matcha_ -> (c1match+1)*matcha")
	this.RepeatRun(es, "matcha_ + matcha_ -> 2*matcha")
	this.RepeatRun(es, "(c1match_Integer*matcha_) + matcha_ -> (c1match+1)*matcha")
	this.RepeatRun(es, "(c1match_Real*matcha_) + (c2match_Integer*matcha_) -> (c1match+c2match)*matcha")

	this.RepeatRun(es, "matcha_^matchb_ / matcha_ -> matcha^(matchb-1)")
	this.RepeatRun(es, "matcha_^matchb_ / matcha_^matchc_ -> matcha^(matchb-matchc)")
	this.RepeatRun(es, "matcha_^matchb_ * matcha_ -> matcha^(matchb+1)")
	this.RepeatRun(es, "matcha_^matchb_ * matcha_^matchc_ -> matcha^(matchb+matchc)")
	return this.Expr
}

func (this *BasicSimplify) Replace(r *Rule, es *EvalState) Ex {
	if this.IsMatchQ(r.Lhs, es) {
		return r.Rhs
	}
	this.Expr = this.Expr.Replace(r, es)
	return this.Eval(es)
}

func (this *BasicSimplify) ToString() string {
	var buffer bytes.Buffer
	buffer.WriteString("BasicSimplify[")
	buffer.WriteString(this.Expr.ToString())
	buffer.WriteString("]")
	return buffer.String()
}

func (this *BasicSimplify) IsEqual(otherEx Ex, es *EvalState) string {
	other, ok := otherEx.(*BasicSimplify)
	if !ok {
		return "EQUAL_UNK"
	}
	return FunctionIsEqual([]Ex{
		this.Expr,
	}, []Ex{
		other.Expr,
	}, es)
}

func (this *BasicSimplify) IsSameQ(otherEx Ex, es *EvalState) bool {
	other, ok := otherEx.(*BasicSimplify)
	if !ok {
		return false
	}
	return FunctionIsSameQ([]Ex{
		this.Expr,
	}, []Ex{
		other.Expr,
	}, es)
}

func (this *BasicSimplify) IsMatchQ(otherEx Ex, es *EvalState) bool {
	if IsBlankType(otherEx, "BasicSimplify") {
		return true
	}
	return this.IsSameQ(otherEx, es)
}

func (this *BasicSimplify) DeepCopy() Ex {
	return &BasicSimplify{
		Expr: this.Expr.DeepCopy(),
	}
}
