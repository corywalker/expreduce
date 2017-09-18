(* ::Package:: *)

(* ::Title:: *)
(*Make Rubi MX file*)


(* ::Subsubtitle:: *)
(*Run this package to generate a fast-loading Rubi4.8.mx file that can be read using a Get ["Rubi4.8.mx"] command.*)


(* ::Subsubtitle:: *)
(*Set the control variable ShowSteps to True before running this package to generate a ShowRubi4.8.mx file that enables Rubi to display the steps required to integrate an expression.*)


(* ::Subsubtitle:: *)
(*Note that MX files cannot be exchanged between different operating systems or versions of Mathematica.*)


ShowSteps=False;


Get[NotebookDirectory[]<>"ShowStep Routines.m"];
Get[NotebookDirectory[]<>"Integration Utility Functions.m"];

Clear[Int];
Int::usage="Int[expn,var] returns the indefinite integral of <expn> with respect to <var>.";

LoadPackage["8.1 Integrand Simplification Rules"];

LoadPackage["1.1 Linear Product Rules"];
LoadPackage["1.2 Quadratic Product Rules"];
LoadPackage["1.3 Binomial Product Rules"];
LoadPackage["1.4 Trinomial Product Rules"];
LoadPackage["1.5 Algebraic Function Rules"];

LoadPackage["8.3 Piecewise Linear Function Rules"];
LoadPackage["2 Exponential Function Rules"];

LoadPackage["3.1 Sine Function Rules"];
LoadPackage["3.2 Tangent Function Rules"];
LoadPackage["3.3 Secant Function Rules"];
LoadPackage["3.4 Trig Function Rules"];

LoadPackage["4 Hyperbolic Function Rules"];

LoadPackage["5 Inverse Trig Function Rules"];

LoadPackage["6 Inverse Hyperbolic Function Rules"];

LoadPackage["7 Special Function Rules"];

LoadPackage["8.2 Derivative Integration Rules"];
LoadPackage["8.4 Miscellaneous Integration Rules"];
FixIntRules[];


If[ShowSteps, StepFunction[Int]];


SetDirectory[NotebookDirectory[]];
DumpSave[If[ShowSteps===True, "StepRubi4.8.mx", "Rubi4.8.mx"], "Global`"];
ResetDirectory[];
