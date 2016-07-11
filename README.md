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
> BasicSimplify[(a+b)-(a+b)+c-c+2*c^a+2*d+5*d+d-5*d+3*c^a]
In:  BasicSimplify[((((((((((a + b) + ((a + b) * -1)) + c) + (c * -1)) + (2 * c^a)) + (2 * d)) + (5 * d)) + d) + ((5 * d) * -1)) + (3 * c^a))]
Out: ((5 * c^a) + (3 * d))
> BasicSimplify[a^2*a^c]
In:  BasicSimplify[(a^2 * a^c)]
Out: a^(2 + c)
```

## Development

To run the tests:
```
go test
```
