Echo[expr_] := (
    Print[expr];
    expr
);

ExpreduceSetLogging::usage = "`ExpreduceSetLogging[bool, level]` sets the logging state to `bool` and the level to `level`.";
Attributes[ExpreduceSetLogging] = {Protected};

ExpreduceDefinitionTimes::usage = "`ExpreduceDefinitionTimes[]` prints the time in seconds evaluating various definitions.";
Attributes[ExpreduceDefinitionTimes] = {Protected};

Attributes::usage = "`Attributes[sym]` returns a `List` of attributes for `sym`.";
Attributes[Attributes] = {HoldAll, Listable, Protected};
Tests`Attributes = {
    ESimpleExamples[
        ESameTest[{Protected, ReadProtected}, Attributes[Infinity]],
        ESameTest[{HoldAll, Listable, Protected}, Attributes[Attributes]],
        ESameTest[{Flat, Listable, NumericFunction, OneIdentity, Orderless, Protected}, Attributes[Plus]],
        EComment["The default set of attributes is the empty list:"],
        ESameTest[{}, Attributes[undefinedSym]]
    ], EFurtherExamples[
        EComment["Only symbols can have attributes:"],
        ESameTest[Attributes[2], Attributes[2]],
        ESameTest[Attributes[a^2], Attributes[a^2]]
    ]
};

Default::usage = "`Default[sym]` returns the default value of `sym` when used as an `Optional` pattern without a default specified.";
Attributes[Default] = {Protected};
Tests`Default = {
    ESimpleExamples[
        ESameTest[1, Default[Times]],
        ESameTest[0, Default[Plus]]
    ], ETests[
        ESameTest[Default[foo], Default[foo]]
    ]
};

Clear::usage = "`Clear[sym1, sym2, ...]` clears the symbol definitions from the evaluation context.";
Attributes[Clear] = {HoldAll, Protected};
Tests`Clear = {
    ESimpleExamples[
        ESameTest[a, a],
        ESameTest[5, a = 5],
        ESameTest[6, b = 6],
        ESameTest[7, c = 7],
        ESameTest[5, a],
        ESameTest[Null, Clear[a, 99, b]],
        ESameTest[Symbol, Head[a]],
        ESameTest[Symbol, Head[b]],
        ESameTest[Integer, Head[c]],
        ESameTest[Null, Clear[c]],
        ESameTest[Symbol, Head[c]]
    ]
};

Timing::usage = "`Timing[expr]` returns a `List` with the first element being the time in seconds for the evaluation of `expr`, and the second element being the result.";
Attributes[Timing] = {HoldAll, SequenceHold, Protected};
Tests`Timing = {
    ESimpleExamples[
        EExampleOnlyInstruction["{0.00167509, 5000000050000000}", "Timing[Sum[a, {a, 100000000}]]"]
    ]
};

MessageName::usage = "`sym::msg` references a particular message for `sym`.";
Attributes[MessageName] = {HoldFirst, ReadProtected, Protected};
Tests`MessageName = {
    ESimpleExamples[
        EComment["`MessageName` is used to store the usage messages of built-in symbols:"],
        ESameTest["`sym::msg` references a particular message for `sym`.", MessageName::usage]
    ]
};

Trace::usage = "`Trace[expr]` traces the evaluation of `expr`.";
Attributes[Trace] = {HoldAll, Protected};
Tests`Trace = {
    ESimpleExamples[
        ESameTest[List[HoldForm[Plus[1, 2]], HoldForm[3]], 1 + 2 // Trace],
        ESameTest[List[List[HoldForm[Plus[1, 3]], HoldForm[4]], HoldForm[Plus[4, 2]], HoldForm[6]], (1 + 3) + 2 // Trace],
        ESameTest[List[List[HoldForm[Plus[1, 3]], HoldForm[4]], HoldForm[Plus[2, 4]], HoldForm[6]], 2 + (1 + 3) // Trace]
    ], ETests[
        ESameTest[{}, Trace[a + b + c]],
        ESameTest[{}, Trace[1]],
        ESameTest[{HoldForm[2^2], HoldForm[4]}, Trace[2^2]],
        ESameTest[{{HoldForm[2^2], HoldForm[4]}, HoldForm[4*5], HoldForm[20]}, Trace[2^2*5]],
        ESameTest[{{{HoldForm[2^2], HoldForm[4]}, HoldForm[4*5], HoldForm[20]}, HoldForm[20 + 4], HoldForm[24]}, Trace[2^2*5+4]],
        ESameTest[{{{HoldForm[2^2], HoldForm[4]}, {HoldForm[3^3], HoldForm[27]}, HoldForm[4*27*5], HoldForm[540]}, HoldForm[540 + 4], HoldForm[544]}, Trace[2^2*3^3*5+4]],
        ESameTest[{HoldForm[b + a], HoldForm[a + b]}, Trace[b+a]],
        ESameTest[{}, Trace[a+foo[a,b]]],
        ESameTest[{HoldForm[foo[Sequence[a, b]]], HoldForm[foo[a, b]]}, Trace[foo[Sequence[a,b]]]]
    ], EKnownFailures[
        ESameTest[{{{HoldForm[a*a], HoldForm[a^2]}, HoldForm[foo[a^2, b]]}, HoldForm[a + foo[a^2, b]]}, Trace[a+foo[a*a,b]]]
    ]
};

N::usage = "`N[expr]` attempts to convert `expr` to a numeric value.";
Attributes[N] = {Protected};
Tests`N = {
    ETests[
        ESameTest[2., N[2]],
        ESameTest[0.5, N[1/2]]
    ]
};

Listable::usage = "`Listable` is an attribute that calls for functions to automatically map over lists.";
Attributes[Listable] = {Protected};
Tests`Listable = {
    ESimpleExamples[
        ESameTest[{1, 1, 1, 0}, Boole[{True, True, True, False}]],
        ESameTest[{False, True, True}, Positive[{-1, 4, 5}]],
        ESameTest[{{False, True, True}}, Positive[{{-1, 4, 5}}]],
        ESameTest[{{False, True, True}, {True, False}}, Positive[{{-1, 4, 5}, {6, -1}}]]
    ], ETests[
        ESameTest[{Positive[-1, 2], Positive[4, 2], Positive[5, 2]}, Positive[{-1, 4, 5}, 2]],
        ESameTest[Positive[{-1, 4, 5}, {1, 2}], Positive[{-1, 4, 5}, {1, 2}]],
        ESameTest[{Positive[-1, 1], Positive[4, 2], Positive[5, 3]}, Positive[{-1, 4, 5}, {1, 2, 3}]]
    ]
};

Get::usage = "`Get[file]` loads `file` and returns the last expression.";
Attributes[Get] = {Protected};

Module::usage = "`Module[{locals}, expr]` evaluates `expr` with the local variables `locals`.";
Attributes[Module] = {HoldAll, Protected};
Tests`Module = {
    EKnownFailures[
        (*The numbers are off by N here because the symbols get marked as seen*)
        (*upon parsing, probably.*)
        ESameTest[{t$1,j$1,2}, $ModuleNumber=1;Module[{t,j},{t,j,$ModuleNumber}]],
        ESameTest[{t$2,j$2,3}, $ModuleNumber=1;Module[{t,j},{t,j,$ModuleNumber}]],
        ESameTest[{t$4,j$4,5}, $ModuleNumber=1;t$3=test;Module[{t,j},{t,j,$ModuleNumber}]],
        ESameTest[{t$8,2,9}, $ModuleNumber=8;t$3=test;Module[{t,j=2},{t,j,$ModuleNumber}]],
        ESameTest[{t$9,2,10}, $ModuleNumber=8;t$3=test;Module[{t,j:=2},{t,j,$ModuleNumber}]]
    ]
};

(* TODO: Fix this hack. *)
Block[args___] := Module[args];
Attributes[Block] = {HoldAll, Protected};

Hash::usage = "`Hash[expr]` returns an integer hash of `expr`.";
Attributes[Hash] = {Protected};

BeginPackage::usage = "`BeginPackage[context]` updates the context and sets the context path to only the current context and System.";
Attributes[BeginPackage] = {Protected};
BeginPackage[c_String] := (
    $ExpreduceOldContext = $Context;
    $Context = c;
    $ExpreduceOldContextPath = $ContextPath;
    $ContextPath = {c, "System`"};

    $ExpreducePkgContext = c;
);

EndPackage::usage = "`EndPackage[]` resets the contexts to the original values, but with the package context prepended.";
Attributes[EndPackage] = {Protected};
EndPackage[] := (
    $Context = $ExpreduceOldContext;
    $ExpreduceOldContext = Null;
    $ContextPath = Prepend[$ExpreduceOldContextPath, $ExpreducePkgContext];
    $ExpreduceOldContextPath = Null;

    $ExpreducePkgContext = Null;
);

Begin::usage = "`Begin[context]` updates the context.";
Attributes[Begin] = {Protected};
Begin[c_String] := (
    $ExpreduceOldContext2 = $Context;
    If[StringTake[c, {1, 1}] == "`",
        $Context = $Context <> StringTake[c, {2, StringLength[c]}],
        $Context = c
    ];
    $Context
);

End::usage = "`End[]` updates the context to rever the changes caused by `Begin`.";
Attributes[End] = {Protected};
End[] := (
    expreduceToReturn = $Context;
    $Context = $ExpreduceOldContext2;
    expreduceToReturn
);

PrintTemporary::usage = "`PrintTemporary[expr1, expr2, ...]` prints the string representation of the expressions to the console and returns `Null`.";
Attributes[PrintTemporary] = {Protected};
PrintTemporary[exprs___] := Print[exprs];

SetAttributes::usage = "`SetAttributes[sym, attributes]` adds the `attributes` to `sym`.";
Attributes[SetAttributes] = {HoldFirst, Protected};
SetAttributes[s_Symbol, attr_Symbol] := SetAttributes[s, {attr}];
SetAttributes[s_Symbol, attrs_List] := (
    Attributes[s] = Union[Attributes[s], attrs];
);
SetAttributes[l_List, attrs_] := Scan[SetAttributes[#, attrs]&, l];

ClearAttributes::usage = "`ClearAttributes[sym, attributes]` clears the `attributes` from `sym`.";
Attributes[ClearAttributes] = {HoldFirst, Protected};
ClearAttributes[s_Symbol, attr_Symbol] := ClearAttributes[s, {attr}];
ClearAttributes[s_Symbol, attrs_List] := (
    Attributes[s] = Complement[Attributes[s], attrs];
);
ClearAttributes[l_List, attrs_] := Scan[ClearAttributes[#, attrs]&, l];

Protect::usage = "`Protect[sym]` adds the `Protected` attribute to `sym`.";
Attributes[Protect] = {HoldAll, Protected};
Protect[s_Symbol] := SetAttributes[s, {Protected}];

Unprotect::usage = "`Unprotect[sym]` clears the `Protected` attribute from `sym`.";
Attributes[Unprotect] = {HoldAll, Protected};
Unprotect[s_Symbol] := ClearAttributes[s, {Protected}];

Quiet::usage = "`Quiet[e]` runs `e` without printing any messages.";
Attributes[Quiet] = {HoldAll, Protected};
Quiet[e_] := e;

ReadList::usage = "`ReadList[file]` reads expressions in `file` into a list.";
Attributes[ReadList] = {Protected};

TimeConstrained::usage = "`TimeConstrained[expr, limit]` evaluates `expr` but expires after `limit`.";
(*TODO: Perhaps we can convert the checks to HasThrown to be more generic.*)
(*They can just check if we should abort and return a certain vailue*)
Attributes[TimeConstrained] = {HoldAll, Protected};
TimeConstrained[e_, t_] := TimeConstrained[e, t, $Aborted];
(* Hack just to get this function returning useful values for Rubi. *)
TimeConstrained[e_, t_, f_] := e;

Throw::usage = "`Throw[e]` stops all execution, propagating the value down with the intention of it being caught. Only some of the flow control statements in the language actually support execution interruption right now.";
Attributes[Throw] = {Protected};

Catch::usage = "`Catch[e]` catches and returns any `Thrown` expressions, if any. Otherwise returns the result of `e`.";
Attributes[Catch] = {HoldFirst, Protected};
Tests`Catch = {
    ESimpleExamples[
        ESameTest[c, Catch[a; b; Throw[c]; d; e]],
        ESameTest[c, Catch[{a, b, Throw[c], d}]]
    ]
};

DownValues::usage = "`DownValues[sym]` returns a list of downvalues for `sym`.";
Attributes[DownValues] = {HoldAll, Protected};
Tests`DownValues = {
    ETests[
        ESameTest[Null, ClearAll[myfoo]],
        ESameTest[Null, myfoo[_] := a /; b;],
        ESameTest[1, Length[DownValues[myfoo]]],
        (*Defining the exact same definition has no effect.*)
        ESameTest[Null, myfoo[_] := a /; b;],
        ESameTest[1, Length[DownValues[myfoo]]],
        (*Defining the same condition but with a different RHS will overwrite.*)
        ESameTest[Null, myfoo[_] := b /; b;],
        ESameTest[1, Length[DownValues[myfoo]]],
        (*While this new definition has the same LHS, the condition on the RHS*)
        (*is different so it should count as a separate DownValue.*)
        ESameTest[Null, myfoo[_] := a /; c;],
        ESameTest[2, Length[DownValues[myfoo]]],
        ESameTest[Null, myfoo[_] := With[{}, a /; c];],
        ESameTest[3, Length[DownValues[myfoo]]],
        ESameTest[Null, myfoo[_] := With[{}, b /; c];],
        ESameTest[3, Length[DownValues[myfoo]]],
        ESameTest[Null, myfoo[_] := With[{a=2}, b /; c];],
        ESameTest[4, Length[DownValues[myfoo]]],
        ESameTest[Null, myfoo[_] := With[{a=3}, b /; c];],
        ESameTest[5, Length[DownValues[myfoo]]],
        ESameTest[Null, myfoo[_] := With[{a=2}, c /; c];],
        ESameTest[5, Length[DownValues[myfoo]]],
        ESameTest[Null, myfoo[_] := With[{a=2}, c /; c] /; True;],
        ESameTest[6, Length[DownValues[myfoo]]],
        ESameTest[6, Length[DownValues[myfoo]]],

        (*Test assignment.*)
        ESameTest[Null, DownValues[dvAssignTest] = {
                HoldPattern[dvAssignTest[1]] :> 123,
                HoldPattern[dvAssignTest[_]] :> 321
            };],
        ESameTest[123, dvAssignTest[1]],
        ESameTest[321, dvAssignTest[2]],
    ]
};

ClearAll::usage = "`ClearAll[s1, s2, ...]` clears all definitions associated with the symbols.";
Attributes[ClearAll] = {HoldAll, Protected};
ClearAll[syms___] := Scan[
   (
      Attributes[#] = {};
      Clear[#];
   )&,
   {syms}
];
Tests`ClearAll = {
    ESimpleExamples[
        ESameTest[{HoldAll}, Attributes[mytestsym] = {HoldAll}],
        ESameTest[Null, mytestsym[5] := 6],
        ESameTest[Null, mytestsym[7] := 8],
        ESameTest[1, Length[Attributes[mytestsym]]],
        ESameTest[2, Length[DownValues[mytestsym]]],
        ESameTest[Null, ClearAll[mytestsym]],
        ESameTest[0, Length[Attributes[mytestsym]]],
        ESameTest[0, Length[DownValues[mytestsym]]]
    ]
};

ExpreduceMaskNonConditional::usage = "`ExpreduceMaskNonConditional[expr]` returns a version of `expr` with the nonconditional part masked out. Used internally for definitions.";
Attributes[ExpreduceMaskNonConditional] = {HoldAll, Protected};
Tests`ExpreduceMaskNonConditional = {
    ETests[
        ESameTest[Hold[ExpreduceNonConditional], ExpreduceMaskNonConditional[a+b]],
        ESameTest[Hold[With[{}, ExpreduceNonConditional /; c]], ExpreduceMaskNonConditional[With[{}, a /; c]]],
        ESameTest[Hold[With[{a=2}, ExpreduceNonConditional /; c] /; True], ExpreduceMaskNonConditional[With[{a=2}, c /; c] /; True]],
        ESameTest[Hold[ExpreduceNonConditional], ExpreduceMaskNonConditional[With[{}, a]]],
    ]
};

Unique::usage = "`Unique[]` returns a unique symbol.";
Attributes[Unique] = {Protected};

Attributes[Defer] = {HoldAll, Protected, ReadProtected};
