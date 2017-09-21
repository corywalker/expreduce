LoadRubi::usage = "`LoadRubi[]` will load the Rubi integration package by Albert Rich.";
LoadRubi[] := Get["__res__/rubi_loader.m"];
Attributes[LoadRubi] = {Protected};
Tests`LoadRubi = {
    ESimpleExamples[
        (*Just test a few cases for a sanity check. Full test suite can be run
        outside of test suite.*)
        ESameTest[Null, LoadRubi[]],
        ESameTest[x^3/3 + 2*x, Rubi`Int[x^2+2, x]],
        ESameTest[Log[x], Rubi`Int[1/x, x]],
        ESameTest[-(a/(4 x^4))-b/(3 x^3), Rubi`Int[(a+b x)/x^5,x]],
        ESameTest[-((3/2+2 x)^2/(3 x^2)), Rubi`Int[(3/2+2 x)/x^3,x]],
    ], ETests[
        ESameTest[x^3/3, Rubi`Int[x^2, x]],
        (*ESameTest[Null, therule = (HoldPattern[Rubi`Int[((a_ + (c_. * x_^2))^-1/2 * (d_ + (e_. * x_))^m_), x_Symbol]]) :> (Condition[(2 * a * Rubi`Private`Rt[((c * -1) * a^-1), 2] * (d + (e * x))^m * (Sqrt[(1 + (c * (x^2 * a^-1)))] * (c * Sqrt[(a + (c * x^2))] * (c * ((d + (e * x)) * ((c * d) + ((a * e * Rubi`Private`Rt[((c * -1) * a^-1), 2]) * -1))^-1))^m)^-1) * Rubi`Subst[Rubi`Int[((1 + (2 * a * e * Rubi`Private`Rt[((c * -1) * a^-1), 2] * (x^2 * ((c * d) + ((a * e * Rubi`Private`Rt[((c * -1) * a^-1), 2]) * -1))^-1)))^m * Sqrt[(1 + (x^2 * -1))]^-1), x], x, Sqrt[((1 + ((Rubi`Private`Rt[((c * -1) * a^-1), 2] * x) * -1)) * 2^-1)]]), (FreeQ[{a, c, d, e}, x] && Rubi`Private`NeQ[((c * d^2) + (a * e^2))] && Rubi`Private`EqQ[(m^2 + ((1 * 4^-1) * -1))])]);],*)
        (*ESameTest[Null, Rubi`Private`FixIntRule[therule,x];Rubi`Private`FixIntRule[therule,x];Rubi`Private`FixIntRule[therule,x];Rubi`Private`FixIntRule[therule,x];Rubi`Private`FixIntRule[therule,x];Rubi`Private`FixIntRule[therule,x];Rubi`Private`FixIntRule[therule,x];Rubi`Private`FixIntRule[therule,x];Rubi`Private`FixIntRule[therule,x];Rubi`Private`FixIntRule[therule,x];Rubi`Private`FixIntRule[therule,x];Rubi`Private`FixIntRule[therule,x];Rubi`Private`FixIntRule[therule,x];Rubi`Private`FixIntRule[therule,x];Rubi`Private`FixIntRule[therule,x];Rubi`Private`FixIntRule[therule,x];Rubi`Private`FixIntRule[therule,x];Rubi`Private`FixIntRule[therule,x];Rubi`Private`FixIntRule[therule,x];Rubi`Private`FixIntRule[therule,x];Rubi`Private`FixIntRule[therule,x];Rubi`Private`FixIntRule[therule,x];],*)
    ], EKnownFailures[
        (*Will not work until we add support for FixIntRules. Coefficients
        will not distribute.*)
        ESameTest[-(3/8) ArcTanh[Cos[a+x]]-3/8 Cot[a+x] Csc[a+x]-1/4 Cot[a+x] Csc[a+x]^3, Rubi`Int[csc[a+x]^5,x]],
    ]
};
