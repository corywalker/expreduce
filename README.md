This software is experimental quality and is not currently intended for serious use. There are plenty of more mature open source computer algebra systems to use instead.

# Source generation
Generate source files from lex and yacc:
```
go generate
```

# Example
This must be done after running "go generate". To run the example CAS prompt:

```
cd example
go run calc.go
```

```
# go run calc.go
> y=a*a
In:  (y) = ((a * a))
Out: (a * a)
> y=y*y
In:  (y) = ((y * y))
Out: (a * a * a * a)
> a=2
In:  (a) = (2)
Out: 2
> y
In:  y
Out: 16
```

## Development

To run the tests:
```
go test
```
