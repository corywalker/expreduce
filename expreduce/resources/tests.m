
Tests`ExpreduceMiscTests = {
  ETests[
    ESameTest[1/2 E^((I Pi)/4), z=1/2 E^(\[ImaginaryJ]*Pi/4)],
    ESameTest[1/(2 Sqrt[2]), Re[z]],
    ESameTest[1/(2 Sqrt[2]), 1/2*Cos[Pi/4]],
    ESameTest[1/(2 Sqrt[2]), Im[z]],
    ESameTest[1/(2 Sqrt[2]), 1/2*Sin[Pi/4]],
    ESameTest[1/2, Abs[z]],
    ESameTest[Pi/4, Arg[z]],
    ESameTest[-(1/(2 Sqrt[2])), Conjugate[z]//Im],
    ESameTest[1/Sqrt[2], z+Conjugate[z]//FullSimplify],
    ESameTest[1/Sqrt[2], Cos[Pi/4]],
    ESameTest[{-(1/2),0}, ReIm[1/2 E^(\[ImaginaryJ]*Pi)]],
    ESameTest[{-(1/2),0}, ReIm[1/2 E^(-\[ImaginaryJ]*Pi)]],
    ESameTest[{0,1}, ReIm[E^(\[ImaginaryJ]*Pi/2)]],
    ESameTest[{0,-1}, ReIm[E^(-\[ImaginaryJ]*Pi/2)]],
    ESameTest[{0,1}, ReIm[E^(\[ImaginaryJ]*5Pi/2)]],
    ESameTest[{5,0}, ReIm[5*E^(\[ImaginaryJ](0))]],
    ESameTest[{-2,0}, ReIm[2*E^(\[ImaginaryJ](Pi))]],
    ESameTest[{0,-3}, ReIm[3*E^(\[ImaginaryJ](-Pi/2))]],
    ESameTest[{1/2,-(Sqrt[3]/2)}, ReIm[1*E^(\[ImaginaryJ](-2Pi/6))]],
    ESameTest[{1,1}, ReIm[Sqrt[2]*E^(\[ImaginaryJ](Pi/4))]],
    (* a,b,c *)
    ESameTest[{-Im[E^(10 I t)],Re[E^(10 I t)]}, ReIm[\[ImaginaryJ]*E^(\[ImaginaryJ]*10*t)]],
    (* Period: .6283 *)
    ENearlySameTest[0.628319, 2Pi/10//N],
    ESameTest[Null, myf[t_]:=E^((-1+\[ImaginaryJ])t);],
    ESameTest[True, myf[t]==E^-t*E^(\[ImaginaryJ]*t)],
    (* Always decreasing, not periodic *)
    (* Period: .285*)
    ENearlySameTest[0.285714, 2Pi/(7Pi)//N],
    (* Period: 3.167 (maybe pi) *)
    ENearlySameTest[0.628319, 2Pi/10//N],
    ENearlySameTest[1.5708, 2Pi/4//N],
    ENearlySameTest[3.14159, LCM[2/10,2/4]*Pi//N],
    ENearlySameTest[3.14159, LCM[1/5,1/2]*Pi//N],

    ESameTest[Null, ClearAll[z, myf]],
  ]
};
