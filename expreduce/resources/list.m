List::usage = "`{e1, e2, ...}` groups expressions together.";
Attributes[List] = {Locked, Protected};
Tests`List = {
    ESimpleExamples[
        ESameTest[{1, 2, a}, List[1,2,a]]
    ]
};

Total::usage = "`Total[list]` sums all the values in `list`.";
Total[l__List] := Apply[Plus, l];
Attributes[Total] = {Protected};
Tests`Total = {
    ESimpleExamples[
        ESameTest[10, Total[{1,2,3,4}]]
    ], EFurtherExamples[
        EComment["The total of an empty list is zero:"],
        ESameTest[0, Total[{}]]
    ]
};

Mean::usage = "`Mean[list]` calculates the statistical mean of `list`.";
Mean[l__List] := Total[l]/Length[l];
Attributes[Mean] = {Protected};
Tests`Mean = {
    ESimpleExamples[
        ESameTest[11/2, Mean[{5,6}]]
    ]
};

Table::usage = "`Table[expr, n]` returns a list with `n` copies of `expr`.

`Table[expr, {sym, n}]` returns a list with `expr` evaluated with `sym` = 1 to `n`.

`Table[expr, {sym, m, n}]` returns a list with `expr` evaluated with `sym` = `m` to `n`.";
(*Use a UniqueDefined` prefix, or else Table[i, 5] will return*)
(*incorrect results.*)
Table[a_, b_Integer] := Table[a, {UniqueDefined`i, 1, b}];
Attributes[Table] = {HoldAll, Protected};
Tests`Table = {
    ESimpleExamples[
        ESameTest[{a, a, a, a, a}, Table[a, 5]],
        ESameTest[{5, 6, 7, 8, 9, 10}, Table[i, {i, 5, 10}]],
        EComment["Create a list of the first 10 squares:"],
        ESameTest[{1, 4, 9, 16, 25, 36, 49, 64, 81, 100}, Table[n^2, {n, 1, 10}]],
        EComment["Iteration definitions do not have side effects:"],
        EStringTest["i", "i"],
        ESameTest[22, listTableTestState`i = 22],
        ESameTest[{5, 6, 7, 8, 9, 10}, Table[i, {i, 5, 10}]],
        EStringTest["22", "i"]
    ], EFurtherExamples[
        ESameTest[{0,1,2}, Table[x[99], {x[_], 0, 2}]]
    ], ETests[
        EComment["Test proper evaluation of the iterspec."],
        ESameTest[Null, testn := 5;],
        ESameTest[{1, 2, 3, 4, 5}, Table[i, {i, testn}]]
    ]
};

MemberQ::usage = "`MemberQ[expr, pat]` returns True if any of the elements in `expr` match `pat`, otherwise returns False.";
Attributes[MemberQ] = {Protected};
Tests`MemberQ = {
    ESimpleExamples[
        ESameTest[False, MemberQ[{1, 2, 3}, 0]],
        ESameTest[True, MemberQ[{1, 2, 3}, 1]],
        ESameTest[False, MemberQ[{1, 2, 3}, {1}]],
        EComment["`MemberQ` works with patterns:"],
        ESameTest[True, MemberQ[{1, 2, 3}, _Integer]],
        ESameTest[True, MemberQ[{1, 2, 3}, _]],
        ESameTest[False, MemberQ[{1, 2, 3}, _Real]],
        ESameTest[True, MemberQ[{1, 2, 3}, testmatch_Integer]],
        EStringTest["testmatch", "testmatch"],
        ESameTest[False, MemberQ[a, a]],
        ESameTest[False, MemberQ[a, _]],
        (*More tests to be used in OrderlessIsMatchQ*)
        ESameTest[False, MemberQ[{a, b}, c]],
        ESameTest[True, MemberQ[{a, b}, a]]
    ], EFurtherExamples[
        EComment["`MemberQ` works with BlankSequences:"],
        ESameTest[True, MemberQ[{a, b}, ___]],
        ESameTest[True, MemberQ[{a, b}, __]],
        ESameTest[False, MemberQ[{a, b}, __Integer]],
        ESameTest[False, MemberQ[{a, b}, ___Integer]],
        ESameTest[True, MemberQ[{a, b}, ___Symbol]],
        ESameTest[True, MemberQ[{a, b}, __Symbol]],
        ESameTest[True, MemberQ[{a, b, 1}, __Symbol]],
        ESameTest[True, MemberQ[{a, b, 1}, __Integer]],
        EComment["`expr` need not be a List:"],
        ESameTest[True, MemberQ[bar[a, b, c], a]],
        ESameTest[False, MemberQ[bar[a, b, c], bar]]
    ]
};

Cases::usage = "`Cases[expr, pat]` returns a new `List` of all elements in `expr` that match `pat`.";
Attributes[Cases] = {Protected};
Tests`Cases = {
    ESimpleExamples[
        ESameTest[{5, 2, 3.5, x, y, 4}, Cases[{5, 2, 3.5, x, y, 4}, _]],
        ESameTest[{5,2,4}, Cases[{5, 2, 3.5, x, y, 4}, _Integer]],
        ESameTest[{3.5}, Cases[{5, 2, 3.5, x, y, 4}, _Real]],
        ESameTest[{2,c}, Cases[{b^2,1,a^c},_^e_->e]]
    ], EFurtherExamples[
        EComment["`expr` need not be a list:"],
        ESameTest[{a}, Cases[bar[a, b, c], a]]
    ]
};

DeleteCases::usage = "`DeleteCases[expr, pat]` returns a new expression of all elements in `expr` that do not match `pat`.";
Attributes[DeleteCases] = {Protected};
Tests`DeleteCases = {
    ESimpleExamples[
        ESameTest[{3.5,x,y}, DeleteCases[{5,2,3.5,x,y,4},_Integer]],
        ESameTest[{5,2,x,y,4}, DeleteCases[{5,2,3.5,x,y,4},_Real]],
        ESameTest[x+y, DeleteCases[3.5+x+y,_Real]]
    ]
};

Union::usage = "`Union[expr1, expr2, ...]` returns a sorted union of the items in the expressions.";
Attributes[Union] = {Protected};
Tests`Union = {
    ESimpleExamples[
        ESameTest[{a,b}, Union[{b,a,a,b,a}]],
        ESameTest[{a,b,y,z}, Union[{b,a,a,b,a},{y,z}]],
        ESameTest[foo[a,b,y,z], Union[foo[b,a,a,b,a],foo[y,z]]]
    ], ETests[
        ESameTest[Union[foo[b,a,a,b,a],{y,z}], Union[foo[b,a,a,b,a],{y,z}]],
        ESameTest[{}, Union[]],
        ESameTest[Union[{b,a,a,b,a},z], Union[{b,a,a,b,a},z]],
        ESameTest[{a}, Union[{a}]],
        ESameTest[{List}, Union[{List}]]
    ]
};

Complement::usage = "`Complement[expr1, expr2, ...]` returns a sorted union of the items in the expressions.";
Attributes[Complement] = {Protected};
Tests`Complement = {
    ESimpleExamples[
        ESameTest[{b}, Complement[{a, b}, {a}]],
        ESameTest[{c}, Complement[{a, b, c}, {a}, {b}]]
    ], ETests[
        ESameTest[foo[], Complement[foo[a], foo[a]]],
        ESameTest[Complement[], Complement[]],
        ESameTest[{}, Complement[{}]],
        ESameTest[Complement[{}, foo[a]], Complement[{}, foo[a]]],
        ESameTest[{b, c}, Complement[{a, b, c}, {a}, {_}]],
        ESameTest[{b, c}, Complement[{a, b, c, _}, {a}, {_}]],
        ESameTest[{b, c}, Complement[{a, b, c, _}, {a}, {_}, {}]],
        ESameTest[{b, c}, Complement[{a, c, b, _}, {a}, {_}, {}]],
        ESameTest[{b, c}, Complement[{a, c, c, b, _}, {a}, {_}, {}]]
    ]
};

Range::usage = "`Range[n]` returns a `List` of integers from 1 to `n`.

`Range[m, n]` returns a `List` of integers from `m` to `n`.";
Attributes[Range] = {Listable, Protected};
Tests`Range = {
    ESimpleExamples[
        ESameTest[{1, 2, 3}, Range[3]],
        ESameTest[{2, 3, 4, 5}, Range[2, 5]],
        ESameTest[{}, Range[2, -5]]
    ]
};

Part::usage = "`expr[[i]]` or `Part[expr, i]` returns the `i`th element of `expr`.";
Attributes[Part] = {NHoldRest, ReadProtected, Protected};
Tests`Part = {
    ESimpleExamples[
        EComment["Return the second item in a list:"],
        ESameTest[b, {a, b, c, d}[[2]]],
        EComment["Multi-dimensional indices are supported:"],
        ESameTest[{{1, 4, 9, 16, 25}, {2, 8, 18, 32, 50}, {3, 12, 27, 48, 75}, {4, 16, 36, 64, 100}, {5, 20, 45, 80, 125}}, mat = Table[Table[a*b^2, {b, 5}], {a, 5}]],
        ESameTest[20, mat[[5, 2]]],
        EComment["Use `All` to select along the entire dimension:"],
        ESameTest[{5, 20, 45, 80, 125}, mat[[5, All]]]
    ], EFurtherExamples[
        EComment["Out of bounds issues will prevent the expression from evaluating:"],
        ESameTest[{a}[[2]], Part[{a}, 2]],
        EComment["The input need not be a `List`:"],
        ESameTest[foo, Part[foo[a], 0]],
        EComment["Omitting an index will return the original expression:"],
        ESameTest[i, Part[i]],
        ESameTest[{2,4,6}, {{1, 2}, {3, 4}, {5, 6}}[[All, 2]]]
    ], ETests[
        ESameTest[i, Part[i]],
        ESameTest[Part[], Part[]],
        ESameTest[{a, b}[[1.5]], Part[{a, b}, 1.5]],
        ESameTest[{a, b}[[a, 1.5]], Part[{a, b}, a, 1.5]],
        ESameTest[foo, Part[foo[a], 0]],
        ESameTest[{{1, 4, 9, 16, 25}, {2, 8, 18, 32, 50}, {3, 12, 27, 48, 75}, {4, 16, 36, 64, 100}, {5, 20, 45, 80, 125}}, mat = Table[Table[a*b^2, {b, 5}], {a, 5}]],
        ESameTest[20, mat[[5, 2]]],
        ESameTest[{5, 20, 45, 80, 125}, mat[[5, All]]],
        ESameTest[foo[a, b, c], foo[a, b, c][[All]]],
        ESameTest[1[[5]], Part[1, 5]],
        ESameTest[a, Part[{a}, 1]],
        ESameTest[{a}[[2]], Part[{a}, 2]],
        ESameTest[{5, 20, 45, 80, 125}, mat[[All]][[5]]],
        ESameTest[3, {{1, 2}, {3, 4}}[[2, 1]]],
        ESameTest[{{1, 2}, {3}}[[2, 2]], {{1, 2}, {3}}[[2, 2]]],
        ESameTest[{3,4}, {{1, 2}, {3, 4}, {5, 6}}[[2, All]]],
        ESameTest[{25, 50, 75, 100, 125}, mat[[All, 5]]]
    ], EKnownFailures[
        ESameTest[Integer[], Part[1, All]],
        ESameTest[Symbol[], Part[a, All]]
    ]
};

Span::usage = "`start ;; end` represents an index span to select using Part.";
Attributes[Span] = {Protected};
Tests`Span = {
    ESimpleExamples[
        ESameTest[{b, c}, {a, b, c, d}[[2 ;; 3]]],
        ESameTest[{b, c, d}, {a, b, c, d}[[2 ;; All]]]
    ]
};

All::usage = "`All` allows selection along a dimension in `Part`.";
Attributes[All] = {Protected};
Tests`All = {
    ESimpleExamples[
        ESameTest[{{1, 4, 9, 16, 25}, {2, 8, 18, 32, 50}, {3, 12, 27, 48, 75}, {4, 16, 36, 64, 100}, {5, 20, 45, 80, 125}}, mat = Table[Table[a*b^2, {b, 5}], {a, 5}]],
        EComment["Use `All` to select along the entire dimension:"],
        ESameTest[{5, 20, 45, 80, 125}, mat[[5, All]]]
    ]
};

Thread::usage = "`Thread[f[a1, a2, ...}]]` applies f over the arguments, expanding out any lists.";
Attributes[Thread] = {Protected};
Tests`Thread = {
    ETests[
        ESameTest[{f[x], f[y], f[z]}, Thread[f[{x, y, z}]]],
        ESameTest[{f[x, b], f[y, b], f[z, b]}, Thread[f[{x, y, z}, b]]],
        ESameTest[f[{x, y, z}, {b}], Thread[f[{x, y, z}, {b}]]],
        ESameTest[{f[{x, y, z}, b]}, Thread[f[{{x, y, z}}, {b}]]],
        ESameTest[{f[{x, y, z}, b]}, Thread[f[{{x, y, z}}, b]]],
        ESameTest[{f[x, b, a], f[y, b, b], f[z, b, c]}, Thread[f[{x, y, z}, b, {a, b, c}]]],
        ESameTest[{mypos[-1], mypos[4], mypos[5]}, Thread[mypos[{-1, 4, 5}]]],
        ESameTest[f[a, b, c], Thread[f[a, b, c]]],
        ESameTest[{f[1]}, Thread[f[{1}]]],
        ESameTest[{0, 1, 2}, Thread[{0, 1, 2}]],
        ESameTest[{{0, a}, {1, a}, {2, a}}, Thread[{{0, 1, 2}, a}]],
        ESameTest[a, Thread[a]],
        ESameTest[Thread[], Thread[]]
    ]
};

Append::usage = "`Append[list, e]` returns `list` with `e` appended.";
Attributes[Append] = {Protected};
Tests`Append = {
    ESimpleExamples[
        ESameTest[{a,b,c}, Append[{a,b},c]],
        ESameTest[foo[a,b,c], Append[foo[a,b],c]]
    ]
};

AppendTo::usage = "`AppendTo[list, e]` appends `e` to `list` and returns the modified `list`.";
AppendTo[list_, e_] := (list = Append[list, e]);
Attributes[AppendTo] = {HoldFirst, Protected};
Tests`AppendTo = {
    ESimpleExamples[
        ESameTest[{a,b,c}, l = {a, b}; AppendTo[l, c]; l]
    ]
};

Prepend::usage = "`Prepend[list, e]` returns `list` with `e` prepended.";
Attributes[Prepend] = {Protected};
Tests`Prepend = {
    ESimpleExamples[
        ESameTest[{c,a,b}, Prepend[{a,b},c]],
        ESameTest[foo[c,a,b], Prepend[foo[a,b],c]]
    ]
};

PrependTo::usage = "`PrependTo[list, e]` prepends `e` to `list` and returns the modified `list`.";
PrependTo[list_, e_] := (list = Prepend[list, e]);
Attributes[PrependTo] = {HoldFirst, Protected};
Tests`PrependTo = {
    ESimpleExamples[
        ESameTest[{c,a,b}, l = {a, b}; PrependTo[l, c]; l]
    ]
};

DeleteDuplicates::usage = "`DeleteDuplicates[list]` returns `list` with the duplicates removed.";
Attributes[DeleteDuplicates] = {Protected};
Tests`DeleteDuplicates = {
    ESimpleExamples[
        ESameTest[{b,a}, DeleteDuplicates[{b,a,b}]],
        ESameTest[foo[b,a], DeleteDuplicates[foo[b,a,b]]],
        ESameTest[{}, DeleteDuplicates[{}]],
        ESameTest[10000, Length[DeleteDuplicates[Range[10000]]]]
    ]
};

Last::usage = "`Last[expr]` returns the last part of `expr`.";
Last[e_?((Length[#]>=1)&)] := e[[Length[e]]];
Attributes[Last] = {Protected};
Tests`Last = {
    ESimpleExamples[
        ESameTest[6, Last[{1,5,6}]],
        ESameTest[b, Last[a+b]]
    ], ETests[
        ESameTest[Last[a], Last[a]],
        ESameTest[Last[{}], Last[{}]],
        ESameTest[a, Last[{a}]]
    ]
};

First::usage = "`First[expr]` returns the first part of `expr`.";
First[e_?((Length[#]>=1)&)] := e[[1]];
Attributes[First] = {Protected};
Tests`First = {
    ESimpleExamples[
        ESameTest[1, First[{1,5,6}]],
        ESameTest[a, First[a+b]]
    ], ETests[
        ESameTest[First[a], First[a]],
        ESameTest[First[{}], First[{}]],
        ESameTest[a, First[{a}]]
    ]
};

Rest::usage = "`Rest[expr]` returns all but the first part of `expr`.";
Rest[e_?((Length[#]>=1)&)] := e[[2;;All]];
Attributes[Rest] = {Protected};
Tests`Rest = {
    ESimpleExamples[
        ESameTest[{5,6}, Rest[{1,5,6}]],
        ESameTest[b+c, Rest[a+b+c]]
    ], ETests[
        ESameTest[Rest[a], Rest[a]],
        ESameTest[Rest[{}], Rest[{}]],
        ESameTest[{}, Rest[{a}]]
    ]
};

Select::usage = "`Select[expr, cond]` selects only parts of `expr` that satisfy `cond`.";
Attributes[Select] = {Protected};
Tests`Select = {
    ESimpleExamples[
        ESameTest[{1,3,5,7,9,11,13,15,17,19}, Select[Range[20],OddQ]],
        ESameTest[{1,2,3,4}, Select[{1,2,3,4},(True)&]],
        ESameTest[{1,2}, Select[{1,2,3,4},(True)&,2]]
    ], ETests[
        ESameTest[{}, Select[{1,2,3,4},(False)&]],
        ESameTest[{}, Select[{1,2,3,4},(hello)&]],
        ESameTest[foo[2,4], Select[foo[1,2,3,4],(EvenQ[#])&]],
        ESameTest[Select[foo[1,2,3,4]], Select[foo[1,2,3,4]]],
        ESameTest[foo[], Select[foo[1,2,3,4],notfunction]],
        ESameTest[Select[2,EvenQ], Select[2,EvenQ]]
    ]
};

ListQ::usage = "`ListQ[expr]` checks if `expr` has a head of `List`.";
ListQ[expr_] := Head[expr] === List;
Attributes[ListQ] = {Protected};
Tests`ListQ = {
    ESimpleExamples[
        ESameTest[True, ListQ[{a}]],
        ESameTest[False, ListQ[a]],
        ESameTest[True, ListQ[{}]]
    ]
};

Scan::usage = "`Scan[fn, list]` evaluates `fn[elem]` for each element in `list`.";
Attributes[Scan] = {Protected};
Tests`Scan = {
    ESimpleExamples[
        ESameTest[6, Scan[(If[# > 5, Return[#]]) &, {1, 6, 9}]],
        ESameTest[False, Catch[Scan[Function[If[IntegerQ[#], Null, Throw[False]]], {a}]; True]],
        ESameTest[True, Catch[Scan[Function[If[IntegerQ[#], Null, Throw[False]]], {1, 2}]; True]],
        ESameTest[False, Catch[Scan[Function[If[IntegerQ[#], Null, Throw[False]]], {1, a}]; True]]
    ]
};

Join::usage = "`Join[l1, l2, ...]` joins the lists into a single list.";
Attributes[Join] = {Flat, OneIdentity, Protected};
Tests`Join = {
    ESimpleExamples[
        ESameTest[{a,b,c}, Join[{a},{b,c}]],
        ESameTest[{}, Join[]],
        ESameTest[foo[a,b,c], Join[foo[a],foo[b,c]]]
    ]
};

Count::usage = "`Count[l, pattern]` returns the number of expressions in `l` matching `pattern`.";
Count[l_, pattern_] := Count[l, pattern, {1}];
Attributes[Count] = {Protected};
Tests`Count = {
    ESimpleExamples[
        ESameTest[3, Count[a+b+c^2,_]],
        ESameTest[5, Count[a+b+c^2,_,-1]],
        ESameTest[5, Count[a+b+c^2,_,Infinity]],
        ESameTest[0, Count[a,_,Infinity]],
        ESameTest[0, Count[a,_,-1]],
        ESameTest[2, Count[a + 2 + c^2, _Integer, Infinity]],
    ]
};

Tally::usage = "`Tally[list]` creates tallies of the elements in `list`.";
Tally[l_List] := {#, Count[l, #]} & /@ DeleteDuplicates[l];
Attributes[Tally] = {Protected};
Tests`Tally = {
    ESimpleExamples[
        ESameTest[{{a, 2}, {b, 2}}, Tally[{a, a, b, b}]],
        ESameTest[{{b, 2}, {a, 2}}, Tally[{b, b, a, a}]],
        ESameTest[{{b, 2}, {a, 1}}, Tally[{b, b, a}]],
    ]
};

ConstantArray::usage = "`ConstantArray[c, n]` creates a list of `n` copies of `c`.";
Attributes[ConstantArray] = {Protected};
ConstantArray[c_, n_Integer] := Table[c, n];
Tests`ConstantArray = {
    ESimpleExamples[
        ESameTest[{a, a, a}, ConstantArray[a, 3]],
    ]
};

Reverse::usage = "`Reverse[list]` evaluates to a reversed copy of `list`.";
Attributes[Reverse] = {Protected};
Tests`Reverse = {
    ESimpleExamples[
        ESameTest[{5, 4, 3, 2, 1}, Reverse[Range[5]]],
    ]
};
