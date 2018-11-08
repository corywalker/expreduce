ColorData[97, i_] := Switch[i,
  1, RGBColor[0.37, 0.5, 0.71],
  2, RGBColor[0.88, 0.6, 0.14],
  True, RGBColor[0.55, 0.7, 0.2]
];

ExpreduceFilterImaginaryPoints[unfilteredPoints_] :=
  Select[unfilteredPoints, (Im[#[[2]]] == 0) &];

Attributes[ExpreducePlotPoints] = {HoldAll};
ExpreduceGetPoints[fn_, range_List] :=
  Module[{nPoints, stepSize, replacedFn, unfilteredPoints},
   nPoints = 500;
   stepSize = (range[[3]] - range[[2]])/nPoints // N;
   replacedFn = fn /. range[[1]] -> varOfIteration;
   unfilteredPoints =
    Table[{varOfIteration, replacedFn // N}, {varOfIteration,
      range[[2]], range[[3]], stepSize}];
   ExpreduceFilterImaginaryPoints[unfilteredPoints]
   ];

Attributes[ExpreduceGetLine] = {HoldAll};
ExpreduceGetLine[fn_, range_List,
   color_] := {Directive[Opacity[1.], color, AbsoluteThickness[1.6]],
   Line[ExpreduceGetPoints[fn, range]]};

Attributes[ExpreduceGetLines] = {HoldAll};
ExpreduceGetLines[fn_, range_List] := Module[{fns},
   fns = If[Head[fn] === List, fn, {fn}];
   Table[ExpreduceGetLine[fns[[i]], range, ColorData[97, i]], {i,
     Length[fns]}]
   ];

Plot::usage = "`Plot[fn, {var, min, max}]` plots `fn` over the range specified.";
Attributes[Plot] = {HoldAll, Protected, ReadProtected}
Plot[fn_, range_List] :=
  Module[{lines, plotPoints, fullRange, displayOptions},
   lines = ExpreduceGetLines[fn, range];
   plotPoints = Join @@ Map[(#[[2]][[1]]) &, lines];
   fullRange = {MinMax[Join[plotPoints[[All, 1]], range[[2 ;; 3]]]],
     MinMax[plotPoints[[All, 2]]]};
   displayOptions = {DisplayFunction -> Identity,
     AspectRatio -> GoldenRatio^(-1), Axes -> {True, True},
     AxesLabel -> {None, None}, AxesOrigin -> {0, 0},
     DisplayFunction :> Identity,
     Frame -> {{False, False}, {False, False}},
     FrameLabel -> {{None, None}, {None, None}},
     FrameTicks -> {{Automatic, Automatic}, {Automatic, Automatic}},
     GridLines -> {None, None},
     GridLinesStyle -> Directive[GrayLevel[0.5, 0.4]],
     Method -> {"DefaultBoundaryStyle" -> Automatic,
       "DefaultMeshStyle" -> AbsolutePointSize[6],
       "ScalingFunctions" -> None}, PlotRange -> fullRange,
     PlotRangeClipping -> True,
     PlotRangePadding -> {{Scaled[0.02], Scaled[0.02]}, {Scaled[0.05],
         Scaled[0.05]}}, Ticks -> {Automatic, Automatic}};
   Graphics[lines, displayOptions]];
Tests`Plot = {
    ETests[
        ESameTest[Graphics, Plot[2*Cos[10 t + 1] - Sin[4 t - 1], {t, 0, 10}] // Head],
    ]
};
