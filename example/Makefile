all: calc.go
	#gofmt -l -s -w *.go
	go build $^

calc.go: calc.y
	go tool yacc -p Calc -o $@ $<

clean:
	go clean
	#rm -f tokenizer.go calc.go lex.yy.go y.go y.output *~
	rm -f calc.go y.output *~

nuke: clean
	rm -f calc
