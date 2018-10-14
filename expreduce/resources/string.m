ToString::usage = "`ToString[expr, form]` converts `expr` into a string using printing method `form`.";
ToString[a_] := ToString[a, OutputForm];
Attributes[ToString] = {Protected};
Tests`ToString = {
    ESimpleExamples[
        ESameTest["a^2", ToString[Global`a^2, InputForm]],
        ESameTest["\sin (1)", ToString[Sin[1], TeXForm]],
        ESameTest["Hello World", "Hello World" // ToString]
    ], ETests[
        ESameTest["\sin ()", ToString[Sin[], TeXForm]],
        ESameTest["\sin (1,2)", ToString[Sin[1, 2], TeXForm]],
    ]
};

StringJoin::usage = "`s1 <> s2 <> ...` can join a list of strings into a single string.";
(*For some reason this is fast for StringJoin[Table["x", {k,2000}]/.List->Sequence]*)
(*but slow for StringJoin[Table["x", {k,2000}]]*)
(*StringJoin[{args___}]": "StringJoin[args]",*)
(*This rule runs much faster, probably because it avoids*)
(*OrderlessIsMatchQ*)
StringJoin[list_List] := StringJoin[list /. List->Sequence];
Attributes[StringJoin] = {Flat, OneIdentity, Protected};
Tests`StringJoin = {
    ESimpleExamples[
        ESameTest["Hello World", "Hello" <> " " <> "World"],
        ESameTest["If a=2, then a^2=4", "If a=2, then " <> ToString[Global`a^2, InputForm] <> "=" <> ToString[a^2 /. a -> 2, InputForm]]
    ], EFurtherExamples[
        EComment["The `StringJoin` of nothing is the empty string:"],
        ESameTest["", StringJoin[]],
        EComment["If `StringJoin` receives any non-string arguments, the expression does not evaluate:"],
        ESameTest["Hello" <> 5, StringJoin["Hello", 5]],
        EComment["This function takes `List` arguments as well:"],
        ESameTest["abc", StringJoin[{"a", "b", "c"}]]
    ]
};

Infix::usage = "`Infix[expr, sep]` represents `expr` in infix form with separator `sep` when converted to a string.";
Attributes[Infix] = {Protected};
Tests`Infix = {
    ESimpleExamples[
        ESameTest["bar|fuzz|zip", Infix[foo[Global`bar, Global`fuzz, Global`zip], "|"] // ToString]
    ]
};

StringLength::usage = "`StringLength[s]` returns the length of s.";
Attributes[StringLength] = {Listable, Protected};
Tests`StringLength = {
    ESimpleExamples[
        ESameTest[5, StringLength["Hello"]]
    ]
};

StringTake::usage = "`StringTake[s, {start, end}]` takes a substring of s.";
Attributes[StringTake] = {Protected};
Tests`StringTake = {
    ESimpleExamples[
        ESameTest["h", StringTake["hello", {1, 1}]],
        ESameTest[StringTake["hello", {0, 1}], StringTake["hello", {0, 1}]],
        ESameTest["hello", StringTake["hello", {1, StringLength["hello"]}]],
        ESameTest["", StringTake["hello", {2, 1}]],
        ESameTest[StringTake["hello", {2, 999}], StringTake["hello", {2, 999}]]
    ]
};
