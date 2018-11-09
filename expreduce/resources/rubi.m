LoadRubi::usage = "`LoadRubi[]` will load the Rubi integration package by Albert Rich.";
LoadRubi[] := Get["__res__/rubi_loader.m"];
Attributes[LoadRubi] = {Protected};
Tests`LoadRubi = {
    ESimpleExamples[
        (*Just test a few cases for a sanity check. Full test suite can be run
        outside of test suite.*)
        ESameTest[Null, LoadRubi[]],
        ESameTest[x^3/3 + 2*x, Rubi`Int[x^2+2, x]],
        ESameTest[(-3*ArcTanh[Cosh[a+b*x]])/(8*b)+(3*Coth[a+b*x]*Csch[a+b*x])/(8*b)-(Coth[a+b*x]*Csch[a+b*x]^3)/(4*b), Rubi`Int[Csch[a + b*x]^5,x]],
        ESameTest[Log[x], Rubi`Int[1/x, x]],
        ESameTest[-(a/(4 x^4))-b/(3 x^3), Rubi`Int[(a+b x)/x^5,x]],
    ], ETests[
        ESameTest[x^3/3, Rubi`Int[x^2, x]],
    ], EKnownFailures[
        (*Equal, but SameQ cannot tell:*)
        ESameTest[-((3/2+2 x)^2/(3 x^2)), Rubi`Int[(3/2+2 x)/x^3,x]],
        (*Will not work until we add support for FixIntRules. Coefficients
        will not distribute.*)
        ESameTest[-(3/8) ArcTanh[Cos[a+x]]-3/8 Cot[a+x] Csc[a+x]-1/4 Cot[a+x] Csc[a+x]^3, Rubi`Int[csc[a+x]^5,x]],
    ]
};

expreduceRubiSnapshotLoc = "/tmp/rubi.expred";
LoadRubiSnapshot[] := (
  Get[expreduceRubiSnapshotLoc];
  $ContextPath = Prepend[$ContextPath, "Rubi`"];
);
SaveRubiSnapshot[] := Save[expreduceRubiSnapshotLoc, "Rubi`*"];
