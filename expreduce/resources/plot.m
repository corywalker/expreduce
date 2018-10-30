Attributes[ExpreducePlotPoints] = {HoldAll};
ExpreducePlotPoints[fn_, range_List] :=
  Module[{nPoints, stepSize, replacedFn, unfilteredPoints},
   nPoints = 500;
   stepSize = (range[[3]] - range[[2]])/nPoints // N;
   replacedFn = fn /. range[[1]] -> varOfIteration;
   unfilteredPoints =
    Table[{varOfIteration, replacedFn // N}, {varOfIteration,
      range[[2]], range[[3]], stepSize}];
   Select[unfilteredPoints, (Im[#[[2]]] == 0) &]
   ];

Plot::usage = "`Plot[fn, {var, min, max}]` plots `fn` over the range specified.";
Attributes[Plot] = {HoldAll, Protected, ReadProtected}
Plot[fn_, range_List] := Module[{plotPoints, fullRange, displayOptions},
  plotPoints = ExpreducePlotPoints[fn, range];
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
  Graphics[{{{}, {}, {Directive[Opacity[1.],
       RGBColor[0.37, 0.5, 0.71], AbsoluteThickness[1.6]],
      Line[plotPoints]}}}, displayOptions]];
