grep -R "\*EvalState" . | grep -v ") Eval" | grep -v "_test.go" | grep ".go" | grep -v "this \*EvalState" | grep -v "NewEvalState"
