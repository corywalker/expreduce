all: calc.go tokenizer.go
	#gofmt -l -s -w *.go
	go build $^

tokenizer.go: tokenizer.l
	golex -o $@ $<

calc.go: calc.y
	go tool yacc -p Calc -o $@ $<

clean:
	go clean
	#rm -f tokenizer.go calc.go lex.yy.go y.go y.output *~
	rm -f calc.go y.output *~

nuke: clean
	rm -f calc
