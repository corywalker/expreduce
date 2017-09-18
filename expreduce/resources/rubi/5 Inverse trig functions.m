(* ::Package:: *)

(* ::Section:: *)
(*Inverse Trig Function Rules*)


(* ::Subsection::Closed:: *)
(*5.1.1 (a+b arcsin(c x))^n*)


Int[(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  x*(a+b*ArcSin[c*x])^n - 
  b*c*n*Int[x*(a+b*ArcSin[c*x])^(n-1)/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n>0


Int[(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  x*(a+b*ArcCos[c*x])^n + 
  b*c*n*Int[x*(a+b*ArcCos[c*x])^(n-1)/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n>0


Int[(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
  Sqrt[1-c^2*x^2]*(a+b*ArcSin[c*x])^(n+1)/(b*c*(n+1)) + 
  c/(b*(n+1))*Int[x*(a+b*ArcSin[c*x])^(n+1)/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n<-1


Int[(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
  -Sqrt[1-c^2*x^2]*(a+b*ArcCos[c*x])^(n+1)/(b*c*(n+1)) - 
  c/(b*(n+1))*Int[x*(a+b*ArcCos[c*x])^(n+1)/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c},x] && RationalQ[n] && n<-1


Int[(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
  1/(b*c)*Subst[Int[x^n*Cos[a/b-x/b],x],x,a+b*ArcSin[c*x]] /;
FreeQ[{a,b,c,n},x]


Int[(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
  1/(b*c)*Subst[Int[x^n*Sin[a/b-x/b],x],x,a+b*ArcCos[c*x]] /;
FreeQ[{a,b,c,n},x]





(* ::Subsection::Closed:: *)
(*5.1.2 (d x)^m (a+b arcsin(c x))^n*)


Int[(a_.+b_.*ArcSin[c_.*x_])^n_./x_,x_Symbol] :=
  Subst[Int[(a+b*x)^n/Tan[x],x],x,ArcSin[c*x]] /;
FreeQ[{a,b,c},x] && PositiveIntegerQ[n]


Int[(a_.+b_.*ArcCos[c_.*x_])^n_./x_,x_Symbol] :=
  -Subst[Int[(a+b*x)^n/Cot[x],x],x,ArcCos[c*x]] /;
FreeQ[{a,b,c},x] && PositiveIntegerQ[n]


Int[(d_.*x_)^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  (d*x)^(m+1)*(a+b*ArcSin[c*x])^n/(d*(m+1)) - 
  b*c*n/(d*(m+1))*Int[(d*x)^(m+1)*(a+b*ArcSin[c*x])^(n-1)/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c,d,m},x] && PositiveIntegerQ[n] && NeQ[m+1]


Int[(d_.*x_)^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  (d*x)^(m+1)*(a+b*ArcCos[c*x])^n/(d*(m+1)) + 
  b*c*n/(d*(m+1))*Int[(d*x)^(m+1)*(a+b*ArcCos[c*x])^(n-1)/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c,d,m},x] && PositiveIntegerQ[n] && NeQ[m+1]


Int[x_^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
  x^(m+1)*(a+b*ArcSin[c*x])^n/(m+1) - 
  b*c*n/(m+1)*Int[x^(m+1)*(a+b*ArcSin[c*x])^(n-1)/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c},x] && PositiveIntegerQ[m] && RationalQ[n] && n>0


Int[x_^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
  x^(m+1)*(a+b*ArcCos[c*x])^n/(m+1) + 
  b*c*n/(m+1)*Int[x^(m+1)*(a+b*ArcCos[c*x])^(n-1)/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c},x] && PositiveIntegerQ[m] && RationalQ[n] && n>0


Int[x_^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
  x^m*Sqrt[1-c^2*x^2]*(a+b*ArcSin[c*x])^(n+1)/(b*c*(n+1)) - 
  1/(b*c^(m+1)*(n+1))*Subst[Int[ExpandTrigReduce[(a+b*x)^(n+1),Sin[x]^(m-1)*(m-(m+1)*Sin[x]^2),x],x],x,ArcSin[c*x]] /;
FreeQ[{a,b,c},x] && PositiveIntegerQ[m] && RationalQ[n] && -2<=n<-1


Int[x_^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
  -x^m*Sqrt[1-c^2*x^2]*(a+b*ArcCos[c*x])^(n+1)/(b*c*(n+1)) - 
  1/(b*c^(m+1)*(n+1))*Subst[Int[ExpandTrigReduce[(a+b*x)^(n+1),Cos[x]^(m-1)*(m-(m+1)*Cos[x]^2),x],x],x,ArcCos[c*x]] /;
FreeQ[{a,b,c},x] && PositiveIntegerQ[m] && RationalQ[n] && -2<=n<-1


Int[x_^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
  x^m*Sqrt[1-c^2*x^2]*(a+b*ArcSin[c*x])^(n+1)/(b*c*(n+1)) - 
  m/(b*c*(n+1))*Int[x^(m-1)*(a+b*ArcSin[c*x])^(n+1)/Sqrt[1-c^2*x^2],x] + 
  c*(m+1)/(b*(n+1))*Int[x^(m+1)*(a+b*ArcSin[c*x])^(n+1)/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c},x] && PositiveIntegerQ[m] && RationalQ[n] && n<-2


Int[x_^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
  -x^m*Sqrt[1-c^2*x^2]*(a+b*ArcCos[c*x])^(n+1)/(b*c*(n+1)) + 
  m/(b*c*(n+1))*Int[x^(m-1)*(a+b*ArcCos[c*x])^(n+1)/Sqrt[1-c^2*x^2],x] - 
  c*(m+1)/(b*(n+1))*Int[x^(m+1)*(a+b*ArcCos[c*x])^(n+1)/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c},x] && PositiveIntegerQ[m] && RationalQ[n] && n<-2


Int[x_^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
  1/c^(m+1)*Subst[Int[(a+b*x)^n*Sin[x]^m*Cos[x],x],x,ArcSin[c*x]] /;
FreeQ[{a,b,c,n},x] && PositiveIntegerQ[m]


Int[x_^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
  -1/c^(m+1)*Subst[Int[(a+b*x)^n*Cos[x]^m*Sin[x],x],x,ArcCos[c*x]] /;
FreeQ[{a,b,c,n},x] && PositiveIntegerQ[m]


Int[(d_.*x_)^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(d*x)^m*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,m,n},x]


Int[(d_.*x_)^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(d*x)^m*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,m,n},x]





(* ::Subsection::Closed:: *)
(*5.1.3 (d+e x^2)^p (a+b arcsin(c x))^n*)


(* Int[(a_.+b_.*ArcSin[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  1/(c*Sqrt[d])*Subst[Int[(a+b*x)^n,x],x,ArcSin[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e] && PositiveQ[d] *)


(* Int[(a_.+b_.*ArcCos[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  -1/(c*Sqrt[d])*Subst[Int[(a+b*x)^n,x],x,ArcCos[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e] && PositiveQ[d] *)


Int[1/(Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcSin[c_.*x_])),x_Symbol] :=
  Log[a+b*ArcSin[c*x]]/(b*c*Sqrt[d]) /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e] && PositiveQ[d]


Int[1/(Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcCos[c_.*x_])),x_Symbol] :=
  -Log[a+b*ArcCos[c*x]]/(b*c*Sqrt[d]) /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e] && PositiveQ[d]


Int[(a_.+b_.*ArcSin[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  (a+b*ArcSin[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e] && PositiveQ[d] && NeQ[n+1]


Int[(a_.+b_.*ArcCos[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  -(a+b*ArcCos[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e] && PositiveQ[d] && NeQ[n+1]


Int[(a_.+b_.*ArcSin[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]*Int[(a+b*ArcSin[c*x])^n/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e] && Not[PositiveQ[d]]


Int[(a_.+b_.*ArcCos[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]*Int[(a+b*ArcCos[c*x])^n/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e] && Not[PositiveQ[d]]


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(d+e*x^2)^p,x]},  
  Dist[a+b*ArcSin[c*x],u,x] - b*c*Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e] && PositiveIntegerQ[p]


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(d+e*x^2)^p,x]},  
  Dist[a+b*ArcCos[c*x],u,x] + b*c*Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e] && PositiveIntegerQ[p]


(* Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  x*(d+e*x^2)^p*(a+b*ArcSin[c*x])^n/(2*p+1) + 
  2*d*p/(2*p+1)*Int[(d+e*x^2)^(p-1)*(a+b*ArcSin[c*x])^n,x] - 
  b*c*n*d^p/(2*p+1)*Int[x*(1-c^2*x^2)^(p-1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e] && RationalQ[n,p] && n>0 && p>0 && (IntegerQ[p] || PositiveQ[d]) *)


(* Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  x*(d+e*x^2)^p*(a+b*ArcCos[c*x])^n/(2*p+1) + 
  2*d*p/(2*p+1)*Int[(d+e*x^2)^(p-1)*(a+b*ArcCos[c*x])^n,x] + 
  b*c*n*d^p/(2*p+1)*Int[x*(1-c^2*x^2)^(p-1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e] && RationalQ[n,p] && n>0 && p>0 && (IntegerQ[p] || PositiveQ[d]) *)


Int[Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  x*Sqrt[d+e*x^2]*(a+b*ArcSin[c*x])^n/2 - 
  b*c*n*Sqrt[d+e*x^2]/(2*Sqrt[1-c^2*x^2])*Int[x*(a+b*ArcSin[c*x])^(n-1),x] + 
  Sqrt[d+e*x^2]/(2*Sqrt[1-c^2*x^2])*Int[(a+b*ArcSin[c*x])^n/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e] && RationalQ[n] && n>0


Int[Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  x*Sqrt[d+e*x^2]*(a+b*ArcCos[c*x])^n/2 + 
  b*c*n*Sqrt[d+e*x^2]/(2*Sqrt[1-c^2*x^2])*Int[x*(a+b*ArcCos[c*x])^(n-1),x] + 
  Sqrt[d+e*x^2]/(2*Sqrt[1-c^2*x^2])*Int[(a+b*ArcCos[c*x])^n/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e] && RationalQ[n] && n>0


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  x*(d+e*x^2)^p*(a+b*ArcSin[c*x])^n/(2*p+1) + 
  2*d*p/(2*p+1)*Int[(d+e*x^2)^(p-1)*(a+b*ArcSin[c*x])^n,x] - 
  b*c*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/((2*p+1)*(1-c^2*x^2)^FracPart[p])*
    Int[x*(1-c^2*x^2)^(p-1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e] && RationalQ[n,p] && n>0 && p>0


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  x*(d+e*x^2)^p*(a+b*ArcCos[c*x])^n/(2*p+1) + 
  2*d*p/(2*p+1)*Int[(d+e*x^2)^(p-1)*(a+b*ArcCos[c*x])^n,x] + 
  b*c*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/((2*p+1)*(1-c^2*x^2)^FracPart[p])*
    Int[x*(1-c^2*x^2)^(p-1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e] && RationalQ[n,p] && n>0 && p>0


Int[(a_.+b_.*ArcSin[c_.*x_])^n_./(d_+e_.*x_^2)^(3/2),x_Symbol] :=
  x*(a+b*ArcSin[c*x])^n/(d*Sqrt[d+e*x^2]) - 
  b*c*n/Sqrt[d]*Int[x*(a+b*ArcSin[c*x])^(n-1)/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e] && RationalQ[n] && n>0 && PositiveQ[d]


Int[(a_.+b_.*ArcCos[c_.*x_])^n_./(d_+e_.*x_^2)^(3/2),x_Symbol] :=
  x*(a+b*ArcCos[c*x])^n/(d*Sqrt[d+e*x^2]) + 
  b*c*n/Sqrt[d]*Int[x*(a+b*ArcCos[c*x])^(n-1)/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e] && RationalQ[n] && n>0 && PositiveQ[d]


Int[(a_.+b_.*ArcSin[c_.*x_])^n_./(d_+e_.*x_^2)^(3/2),x_Symbol] :=
  x*(a+b*ArcSin[c*x])^n/(d*Sqrt[d+e*x^2]) - 
  b*c*n*Sqrt[1-c^2*x^2]/(d*Sqrt[d+e*x^2])*Int[x*(a+b*ArcSin[c*x])^(n-1)/(1-c^2*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e] && RationalQ[n] && n>0


Int[(a_.+b_.*ArcCos[c_.*x_])^n_./(d_+e_.*x_^2)^(3/2),x_Symbol] :=
  x*(a+b*ArcCos[c*x])^n/(d*Sqrt[d+e*x^2]) + 
  b*c*n*Sqrt[1-c^2*x^2]/(d*Sqrt[d+e*x^2])*Int[x*(a+b*ArcCos[c*x])^(n-1)/(1-c^2*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e] && RationalQ[n] && n>0


(* Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  -x*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n/(2*d*(p+1)) + 
  (2*p+3)/(2*d*(p+1))*Int[(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n,x] + 
  b*c*n*d^p/(2*(p+1))*Int[x*(1-c^2*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e] && RationalQ[n,p] && n>0 && p<-1 && p!=-3/2 && (IntegerQ[p] || PositiveQ[d]) *)


(* Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  -x*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n/(2*d*(p+1)) + 
  (2*p+3)/(2*d*(p+1))*Int[(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n,x] - 
  b*c*n*d^p/(2*(p+1))*Int[x*(1-c^2*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e] && RationalQ[n,p] && n>0 && p<-1 && p!=-3/2 && (IntegerQ[p] || PositiveQ[d]) *)


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  -x*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n/(2*d*(p+1)) + 
  (2*p+3)/(2*d*(p+1))*Int[(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n,x] + 
  b*c*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(2*(p+1)*(1-c^2*x^2)^FracPart[p])*
    Int[x*(1-c^2*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e] && RationalQ[n,p] && n>0 && p<-1 && p!=-3/2


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  -x*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n/(2*d*(p+1)) + 
  (2*p+3)/(2*d*(p+1))*Int[(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n,x] - 
  b*c*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(2*(p+1)*(1-c^2*x^2)^FracPart[p])*
    Int[x*(1-c^2*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e] && RationalQ[n,p] && n>0 && p<-1 && p!=-3/2


Int[(a_.+b_.*ArcSin[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/(c*d)*Subst[Int[(a+b*x)^n*Sec[x],x],x,ArcSin[c*x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e] && PositiveIntegerQ[n]


Int[(a_.+b_.*ArcCos[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  -1/(c*d)*Subst[Int[(a+b*x)^n*Csc[x],x],x,ArcCos[c*x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e] && PositiveIntegerQ[n]


(* Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
  d^p*(1-c^2*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n+1)/(b*c*(n+1)) + 
  c*d^p*(2*p+1)/(b*(n+1))*Int[x*(1-c^2*x^2)^(p-1/2)*(a+b*ArcSin[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[c^2*d+e] && RationalQ[n] && n<-1 && (IntegerQ[p] || PositiveQ[d]) *)


(* Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
  -d^p*(1-c^2*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n+1)/(b*c*(n+1)) - 
  c*d^p*(2*p+1)/(b*(n+1))*Int[x*(1-c^2*x^2)^(p-1/2)*(a+b*ArcCos[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[c^2*d+e] && RationalQ[n] && n<-1 && (IntegerQ[p] || PositiveQ[d]) *)


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
  Sqrt[1-c^2*x^2]*(d+e*x^2)^p*(a+b*ArcSin[c*x])^(n+1)/(b*c*(n+1)) + 
  c*(2*p+1)*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(b*(n+1)*(1-c^2*x^2)^FracPart[p])*
    Int[x*(1-c^2*x^2)^(p-1/2)*(a+b*ArcSin[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[c^2*d+e] && RationalQ[n] && n<-1


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
  -Sqrt[1-c^2*x^2]*(d+e*x^2)^p*(a+b*ArcCos[c*x])^(n+1)/(b*c*(n+1)) - 
  c*(2*p+1)*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(b*(n+1)*(1-c^2*x^2)^FracPart[p])*
     Int[x*(1-c^2*x^2)^(p-1/2)*(a+b*ArcCos[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[c^2*d+e] && RationalQ[n] && n<-1


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  d^p/c*Subst[Int[(a+b*x)^n*Cos[x]^(2*p+1),x],x,ArcSin[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e] && PositiveIntegerQ[2*p] && (IntegerQ[p] || PositiveQ[d])


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  -d^p/c*Subst[Int[(a+b*x)^n*Sin[x]^(2*p+1),x],x,ArcCos[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e] && PositiveIntegerQ[2*p] && (IntegerQ[p] || PositiveQ[d])


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  d^(p-1/2)*Sqrt[d+e*x^2]/Sqrt[1-c^2*x^2]*Int[(1-c^2*x^2)^p*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e] && PositiveIntegerQ[2*p] && Not[IntegerQ[p] || PositiveQ[d]]


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  d^(p-1/2)*Sqrt[d+e*x^2]/Sqrt[1-c^2*x^2]*Int[(1-c^2*x^2)^p*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e] && PositiveIntegerQ[2*p] && Not[IntegerQ[p] || PositiveQ[d]]


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(d+e*x^2)^p,x]},  
  Dist[a+b*ArcSin[c*x],u,x] - b*c*Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e},x] && NeQ[c^2*d+e] && (PositiveIntegerQ[p] || NegativeIntegerQ[p+1/2])


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(d+e*x^2)^p,x]},  
  Dist[a+b*ArcCos[c*x],u,x] + b*c*Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e},x] && NeQ[c^2*d+e] && (PositiveIntegerQ[p] || NegativeIntegerQ[p+1/2])


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcSin[c*x])^n,(d+e*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e,n},x] && NeQ[c^2*d+e] && IntegerQ[p] && (p>0 || PositiveIntegerQ[n])


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcCos[c*x])^n,(d+e*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e,n},x] && NeQ[c^2*d+e] && IntegerQ[p] && (p>0 || PositiveIntegerQ[n])


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(d+e*x^2)^p*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n,p},x]


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(d+e*x^2)^p*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n,p},x]


Int[(d_+e_.*x_)^p_*(f_+g_.*x_)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  (d+e*x)^FracPart[p]*(f+g*x)^FracPart[p]/(d*f+e*g*x^2)^FracPart[p]*
    Int[(d*f+e*g*x^2)^p*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,n,p},x] && EqQ[e*f+d*g] && EqQ[c^2*f^2-g^2] && Not[IntegerQ[p]]


Int[(d_+e_.*x_)^p_*(f_+g_.*x_)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  (d+e*x)^FracPart[p]*(f+g*x)^FracPart[p]/(d*f+e*g*x^2)^FracPart[p]*
    Int[(d*f+e*g*x^2)^p*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,n,p},x] && EqQ[e*f+d*g] && EqQ[c^2*f^2-g^2] && Not[IntegerQ[p]]





(* ::Subsection::Closed:: *)
(*5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n*)


Int[x_*(a_.+b_.*ArcSin[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  -1/e*Subst[Int[(a+b*x)^n*Tan[x],x],x,ArcSin[c*x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e] && PositiveIntegerQ[n]


Int[x_*(a_.+b_.*ArcCos[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/e*Subst[Int[(a+b*x)^n*Cot[x],x],x,ArcCos[c*x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e] && PositiveIntegerQ[n]


(* Int[x_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n/(2*e*(p+1)) + 
  b*n*d^p/(2*c*(p+1))*Int[(1-c^2*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[c^2*d+e] && RationalQ[n] && n>0 && NeQ[p+1] && (IntegerQ[p] || PositiveQ[d]) *)


(* Int[x_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n/(2*e*(p+1)) - 
  b*n*d^p/(2*c*(p+1))*Int[(1-c^2*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[c^2*d+e] && RationalQ[n] && n>0 && NeQ[p+1] && (IntegerQ[p] || PositiveQ[d]) *)


Int[x_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n/(2*e*(p+1)) + 
  b*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(2*c*(p+1)*(1-c^2*x^2)^FracPart[p])*
    Int[(1-c^2*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[c^2*d+e] && RationalQ[n] && n>0 && NeQ[p+1]


Int[x_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n/(2*e*(p+1)) - 
  b*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(2*c*(p+1)*(1-c^2*x^2)^FracPart[p])*
    Int[(1-c^2*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[c^2*d+e] && RationalQ[n] && n>0 && NeQ[p+1]


Int[(a_.+b_.*ArcSin[c_.*x_])^n_./(x_*(d_+e_.*x_^2)),x_Symbol] :=
  1/d*Subst[Int[(a+b*x)^n/(Cos[x]*Sin[x]),x],x,ArcSin[c*x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e] && PositiveIntegerQ[n]


Int[(a_.+b_.*ArcCos[c_.*x_])^n_./(x_*(d_+e_.*x_^2)),x_Symbol] :=
  -1/d*Subst[Int[(a+b*x)^n/(Cos[x]*Sin[x]),x],x,ArcCos[c*x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e] && PositiveIntegerQ[n]


(* Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n/(d*f*(m+1)) - 
  b*c*n*d^p/(f*(m+1))*Int[(f*x)^(m+1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && EqQ[c^2*d+e] && RationalQ[n] && n>0 && EqQ[m+2*p+3] && NeQ[m+1] && 
  (IntegerQ[p] || PositiveQ[d]) *)


(* Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n/(d*f*(m+1)) + 
  b*c*n*d^p/(f*(m+1))*Int[(f*x)^(m+1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && EqQ[c^2*d+e] && RationalQ[n] && n>0 && EqQ[m+2*p+3] && NeQ[m+1] && 
  (IntegerQ[p] || PositiveQ[d]) *)


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n/(d*f*(m+1)) - 
  b*c*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(f*(m+1)*(1-c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m+1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && EqQ[c^2*d+e] && RationalQ[n] && n>0 && EqQ[m+2*p+3] && NeQ[m+1]


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n/(d*f*(m+1)) + 
  b*c*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(f*(m+1)*(1-c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m+1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && EqQ[c^2*d+e] && RationalQ[n] && n>0 && EqQ[m+2*p+3] && NeQ[m+1]


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])/x_,x_Symbol] :=
  (d+e*x^2)^p*(a+b*ArcSin[c*x])/(2*p) - 
  b*c*d^p/(2*p)*Int[(1-c^2*x^2)^(p-1/2),x] + 
  d*Int[(d+e*x^2)^(p-1)*(a+b*ArcSin[c*x])/x,x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e] && PositiveIntegerQ[p]


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])/x_,x_Symbol] :=
  (d+e*x^2)^p*(a+b*ArcCos[c*x])/(2*p) + 
  b*c*d^p/(2*p)*Int[(1-c^2*x^2)^(p-1/2),x] + 
  d*Int[(d+e*x^2)^(p-1)*(a+b*ArcCos[c*x])/x,x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e] && PositiveIntegerQ[p]


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_]),x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^p*(a+b*ArcSin[c*x])/(f*(m+1)) - 
  b*c*d^p/(f*(m+1))*Int[(f*x)^(m+1)*(1-c^2*x^2)^(p-1/2),x] - 
  2*e*p/(f^2*(m+1))*Int[(f*x)^(m+2)*(d+e*x^2)^(p-1)*(a+b*ArcSin[c*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e] && PositiveIntegerQ[p] && NegativeIntegerQ[(m+1)/2]


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_]),x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^p*(a+b*ArcCos[c*x])/(f*(m+1)) + 
  b*c*d^p/(f*(m+1))*Int[(f*x)^(m+1)*(1-c^2*x^2)^(p-1/2),x] - 
  2*e*p/(f^2*(m+1))*Int[(f*x)^(m+2)*(d+e*x^2)^(p-1)*(a+b*ArcCos[c*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e] && PositiveIntegerQ[p] && NegativeIntegerQ[(m+1)/2]


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(f*x)^m*(d+e*x^2)^p,x]},  
  Dist[a+b*ArcSin[c*x],u,x] - b*c*Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e] && PositiveIntegerQ[p]


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(f*x)^m*(d+e*x^2)^p,x]},  
  Dist[a+b*ArcCos[c*x],u,x] + b*c*Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e] && PositiveIntegerQ[p]


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[x^m*(1-c^2*x^2)^p,x]},  
  Dist[d^p*(a+b*ArcSin[c*x]),u,x] - b*c*d^p*Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e] && IntegerQ[p-1/2] && (PositiveIntegerQ[(m+1)/2] || NegativeIntegerQ[(m+2*p+3)/2]) && 
  p!=-1/2 && PositiveQ[d]


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[x^m*(1-c^2*x^2)^p,x]},  
  Dist[d^p*(a+b*ArcCos[c*x]),u,x] + b*c*d^p*Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e] && IntegerQ[p-1/2] && (PositiveIntegerQ[(m+1)/2] || NegativeIntegerQ[(m+2*p+3)/2]) && 
  p!=-1/2 && PositiveQ[d]


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[x^m*(1-c^2*x^2)^p,x]},
  (a+b*ArcSin[c*x])*Int[x^m*(d+e*x^2)^p,x] - 
  b*c*d^(p-1/2)*Sqrt[d+e*x^2]/Sqrt[1-c^2*x^2]*Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e] && PositiveIntegerQ[p+1/2] && (PositiveIntegerQ[(m+1)/2] || NegativeIntegerQ[(m+2*p+3)/2])


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[x^m*(1-c^2*x^2)^p,x]},
  (a+b*ArcCos[c*x])*Int[x^m*(d+e*x^2)^p,x] + 
  b*c*d^(p-1/2)*Sqrt[d+e*x^2]/Sqrt[1-c^2*x^2]*Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e] && PositiveIntegerQ[p+1/2] && (PositiveIntegerQ[(m+1)/2] || NegativeIntegerQ[(m+2*p+3)/2])


(* Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^p*(a+b*ArcSin[c*x])^n/(f*(m+1)) - 
  2*e*p/(f^2*(m+1))*Int[(f*x)^(m+2)*(d+e*x^2)^(p-1)*(a+b*ArcSin[c*x])^n,x] - 
  b*c*n*d^p/(f*(m+1))*Int[(f*x)^(m+1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e] && RationalQ[m,n,p] && n>0 && p>0 && m<-1 && (IntegerQ[p] || PositiveQ[d]) *)


(* Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^p*(a+b*ArcCos[c*x])^n/(f*(m+1)) - 
  2*e*p/(f^2*(m+1))*Int[(f*x)^(m+2)*(d+e*x^2)^(p-1)*(a+b*ArcCos[c*x])^n,x] + 
  b*c*n*d^p/(f*(m+1))*Int[(f*x)^(m+1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e] && RationalQ[m,n,p] && n>0 && p>0 && m<-1 && (IntegerQ[p] || PositiveQ[d]) *)


Int[(f_.*x_)^m_*Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*Sqrt[d+e*x^2]*(a+b*ArcSin[c*x])^n/(f*(m+1)) - 
  b*c*n*Sqrt[d+e*x^2]/(f*(m+1)*Sqrt[1-c^2*x^2])*Int[(f*x)^(m+1)*(a+b*ArcSin[c*x])^(n-1),x] + 
  c^2*Sqrt[d+e*x^2]/(f^2*(m+1)*Sqrt[1-c^2*x^2])*Int[(f*x)^(m+2)*(a+b*ArcSin[c*x])^n/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e] && RationalQ[m,n] && n>0 && m<-1


Int[(f_.*x_)^m_*Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*Sqrt[d+e*x^2]*(a+b*ArcCos[c*x])^n/(f*(m+1)) + 
  b*c*n*Sqrt[d+e*x^2]/(f*(m+1)*Sqrt[1-c^2*x^2])*Int[(f*x)^(m+1)*(a+b*ArcCos[c*x])^(n-1),x] + 
  c^2*Sqrt[d+e*x^2]/(f^2*(m+1)*Sqrt[1-c^2*x^2])*Int[(f*x)^(m+2)*(a+b*ArcCos[c*x])^n/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e] && RationalQ[m,n] && n>0 && m<-1


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^p*(a+b*ArcSin[c*x])^n/(f*(m+1)) - 
  2*e*p/(f^2*(m+1))*Int[(f*x)^(m+2)*(d+e*x^2)^(p-1)*(a+b*ArcSin[c*x])^n,x] - 
  b*c*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(f*(m+1)*(1-c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m+1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e] && RationalQ[m,n,p] && n>0 && p>0 && m<-1


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^p*(a+b*ArcCos[c*x])^n/(f*(m+1)) - 
  2*e*p/(f^2*(m+1))*Int[(f*x)^(m+2)*(d+e*x^2)^(p-1)*(a+b*ArcCos[c*x])^n,x] + 
  b*c*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(f*(m+1)*(1-c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m+1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e] && RationalQ[m,n,p] && n>0 && p>0 && m<-1


(* Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^p*(a+b*ArcSin[c*x])^n/(f*(m+2*p+1)) + 
  2*d*p/(m+2*p+1)*Int[(f*x)^m*(d+e*x^2)^(p-1)*(a+b*ArcSin[c*x])^n,x] - 
  b*c*n*d^p/(f*(m+2*p+1))*Int[(f*x)^(m+1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e] && RationalQ[n,p] && n>0 && p>0 && Not[RationalQ[m] && m<-1] && 
  (IntegerQ[p] || PositiveQ[d]) && (RationalQ[m] || EqQ[n-1]) *)


(* Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^p*(a+b*ArcCos[c*x])^n/(f*(m+2*p+1)) + 
  2*d*p/(m+2*p+1)*Int[(f*x)^m*(d+e*x^2)^(p-1)*(a+b*ArcCos[c*x])^n,x] + 
  b*c*n*d^p/(f*(m+2*p+1))*Int[(f*x)^(m+1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e] && RationalQ[n,p] && n>0 && p>0 && Not[RationalQ[m] && m<-1] && 
  (IntegerQ[p] || PositiveQ[d]) && (RationalQ[m] || EqQ[n-1]) *)


Int[(f_.*x_)^m_*Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*Sqrt[d+e*x^2]*(a+b*ArcSin[c*x])^n/(f*(m+2)) - 
  b*c*n*Sqrt[d+e*x^2]/(f*(m+2)*Sqrt[1-c^2*x^2])*Int[(f*x)^(m+1)*(a+b*ArcSin[c*x])^(n-1),x] + 
  Sqrt[d+e*x^2]/((m+2)*Sqrt[1-c^2*x^2])*Int[(f*x)^m*(a+b*ArcSin[c*x])^n/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e] && RationalQ[n] && n>0 && Not[RationalQ[m] && m<-1] && (RationalQ[m] || EqQ[n-1])


Int[(f_.*x_)^m_*Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*Sqrt[d+e*x^2]*(a+b*ArcCos[c*x])^n/(f*(m+2)) + 
  b*c*n*Sqrt[d+e*x^2]/(f*(m+2)*Sqrt[1-c^2*x^2])*Int[(f*x)^(m+1)*(a+b*ArcCos[c*x])^(n-1),x] + 
  Sqrt[d+e*x^2]/((m+2)*Sqrt[1-c^2*x^2])*Int[(f*x)^m*(a+b*ArcCos[c*x])^n/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e] && RationalQ[n] && n>0 && Not[RationalQ[m] && m<-1] && (RationalQ[m] || EqQ[n-1])


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^p*(a+b*ArcSin[c*x])^n/(f*(m+2*p+1)) + 
  2*d*p/(m+2*p+1)*Int[(f*x)^m*(d+e*x^2)^(p-1)*(a+b*ArcSin[c*x])^n,x] - 
  b*c*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(f*(m+2*p+1)*(1-c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m+1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e] && RationalQ[n,p] && n>0 && p>0 && Not[RationalQ[m] && m<-1] && 
  (RationalQ[m] || EqQ[n-1])


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^p*(a+b*ArcCos[c*x])^n/(f*(m+2*p+1)) + 
  2*d*p/(m+2*p+1)*Int[(f*x)^m*(d+e*x^2)^(p-1)*(a+b*ArcCos[c*x])^n,x] + 
  b*c*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(f*(m+2*p+1)*(1-c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m+1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e] && RationalQ[n,p] && n>0 && p>0 && Not[RationalQ[m] && m<-1] && 
  (RationalQ[m] || EqQ[n-1])


(* Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n/(d*f*(m+1)) + 
  c^2*(m+2*p+3)/(f^2*(m+1))*Int[(f*x)^(m+2)*(d+e*x^2)^p*(a+b*ArcSin[c*x])^n,x] - 
  b*c*n*d^p/(f*(m+1))*Int[(f*x)^(m+1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,p},x] && EqQ[c^2*d+e] && RationalQ[m,n] && n>0 && m<-1 && IntegerQ[m] && (IntegerQ[p] || PositiveQ[d]) *)


(* Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n/(d*f*(m+1)) + 
  c^2*(m+2*p+3)/(f^2*(m+1))*Int[(f*x)^(m+2)*(d+e*x^2)^p*(a+b*ArcCos[c*x])^n,x] + 
  b*c*n*d^p/(f*(m+1))*Int[(f*x)^(m+1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,p},x] && EqQ[c^2*d+e] && RationalQ[m,n] && n>0 && m<-1 && IntegerQ[m] && (IntegerQ[p] || PositiveQ[d]) *)


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n/(d*f*(m+1)) + 
  c^2*(m+2*p+3)/(f^2*(m+1))*Int[(f*x)^(m+2)*(d+e*x^2)^p*(a+b*ArcSin[c*x])^n,x] - 
  b*c*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(f*(m+1)*(1-c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m+1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,p},x] && EqQ[c^2*d+e] && RationalQ[m,n] && n>0 && m<-1 && IntegerQ[m]


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n/(d*f*(m+1)) + 
  c^2*(m+2*p+3)/(f^2*(m+1))*Int[(f*x)^(m+2)*(d+e*x^2)^p*(a+b*ArcCos[c*x])^n,x] + 
  b*c*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(f*(m+1)*(1-c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m+1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,p},x] && EqQ[c^2*d+e] && RationalQ[m,n] && n>0 && m<-1 && IntegerQ[m]


(* Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  f*(f*x)^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n/(2*e*(p+1)) - 
  f^2*(m-1)/(2*e*(p+1))*Int[(f*x)^(m-2)*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n,x] + 
  b*f*n*d^p/(2*c*(p+1))*Int[(f*x)^(m-1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e] && RationalQ[m,n,p] && n>0 && p<-1 && m>1 && (IntegerQ[p] || PositiveQ[d]) *)


(* Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  f*(f*x)^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n/(2*e*(p+1)) - 
  f^2*(m-1)/(2*e*(p+1))*Int[(f*x)^(m-2)*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n,x] - 
  b*f*n*d^p/(2*c*(p+1))*Int[(f*x)^(m-1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e] && RationalQ[m,n,p] && n>0 && p<-1 && m>1 && (IntegerQ[p] || PositiveQ[d]) *)


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  f*(f*x)^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n/(2*e*(p+1)) - 
  f^2*(m-1)/(2*e*(p+1))*Int[(f*x)^(m-2)*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n,x] + 
  b*f*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(2*c*(p+1)*(1-c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m-1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e] && RationalQ[m,n,p] && n>0 && p<-1 && m>1


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  f*(f*x)^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n/(2*e*(p+1)) - 
  f^2*(m-1)/(2*e*(p+1))*Int[(f*x)^(m-2)*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n,x] - 
  b*f*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(2*c*(p+1)*(1-c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m-1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e] && RationalQ[m,n,p] && n>0 && p<-1 && m>1


(* Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  -(f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n/(2*d*f*(p+1)) + 
  (m+2*p+3)/(2*d*(p+1))*Int[(f*x)^m*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n,x] + 
  b*c*n*d^p/(2*f*(p+1))*Int[(f*x)^(m+1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e] && RationalQ[n,p] && n>0 && p<-1 && Not[RationalQ[m] && m>1] && 
  (IntegerQ[p] || PositiveQ[d]) && (IntegerQ[m] || IntegerQ[p] || n==1) *)


(* Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  -(f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n/(2*d*f*(p+1)) + 
  (m+2*p+3)/(2*d*(p+1))*Int[(f*x)^m*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n,x] - 
  b*c*n*d^p/(2*f*(p+1))*Int[(f*x)^(m+1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e] && RationalQ[n,p] && n>0 && p<-1 && Not[RationalQ[m] && m>1] && 
  (IntegerQ[p] || PositiveQ[d]) && (IntegerQ[m] || IntegerQ[p] || n==1) *)


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  -(f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n/(2*d*f*(p+1)) + 
  (m+2*p+3)/(2*d*(p+1))*Int[(f*x)^m*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n,x] + 
  b*c*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(2*f*(p+1)*(1-c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m+1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e] && RationalQ[n,p] && n>0 && p<-1 && Not[RationalQ[m] && m>1] && 
  (IntegerQ[m] || IntegerQ[p] || n==1)


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  -(f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n/(2*d*f*(p+1)) + 
  (m+2*p+3)/(2*d*(p+1))*Int[(f*x)^m*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n,x] - 
  b*c*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(2*f*(p+1)*(1-c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m+1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e] && RationalQ[n,p] && n>0 && p<-1 && Not[RationalQ[m] && m>1] && 
  (IntegerQ[m] || IntegerQ[p] || n==1)


(* Int[(f_.*x_)^m_*(a_.+b_.*ArcSin[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  f*(f*x)^(m-1)*Sqrt[d+e*x^2]*(a+b*ArcSin[c*x])^n/(e*m) + 
  b*f*n/(c*m*Sqrt[d])*Int[(f*x)^(m-1)*(a+b*ArcSin[c*x])^(n-1),x] + 
  f^2*(m-1)/(c^2*m)*Int[((f*x)^(m-2)*(a+b*ArcSin[c*x])^n)/Sqrt[d+e*x^2],x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e] && RationalQ[m,n] && n>0 && m>1 && PositiveQ[d] && IntegerQ[m] *)


(* Int[(f_.*x_)^m_*(a_.+b_.*ArcCos[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  f*(f*x)^(m-1)*Sqrt[d+e*x^2]*(a+b*ArcCos[c*x])^n/(e*m) - 
  b*f*n*Sqrt[1-c^2*x^2]/(c*m*Sqrt[d+e*x^2])*Int[(f*x)^(m-1)*(a+b*ArcCos[c*x])^(n-1),x] + 
  f^2*(m-1)/(c^2*m)*Int[((f*x)^(m-2)*(a+b*ArcCos[c*x])^n)/Sqrt[d+e*x^2],x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e] && RationalQ[m,n] && n>0 && m>1 && PositiveQ[d] && IntegerQ[m] *)


Int[(f_.*x_)^m_*(a_.+b_.*ArcSin[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  f*(f*x)^(m-1)*Sqrt[d+e*x^2]*(a+b*ArcSin[c*x])^n/(e*m) + 
  b*f*n*Sqrt[1-c^2*x^2]/(c*m*Sqrt[d+e*x^2])*Int[(f*x)^(m-1)*(a+b*ArcSin[c*x])^(n-1),x] + 
  f^2*(m-1)/(c^2*m)*Int[((f*x)^(m-2)*(a+b*ArcSin[c*x])^n)/Sqrt[d+e*x^2],x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e] && RationalQ[m,n] && n>0 && m>1 && IntegerQ[m]


Int[(f_.*x_)^m_*(a_.+b_.*ArcCos[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  f*(f*x)^(m-1)*Sqrt[d+e*x^2]*(a+b*ArcCos[c*x])^n/(e*m) - 
  b*f*n*Sqrt[1-c^2*x^2]/(c*m*Sqrt[d+e*x^2])*Int[(f*x)^(m-1)*(a+b*ArcCos[c*x])^(n-1),x] + 
  f^2*(m-1)/(c^2*m)*Int[((f*x)^(m-2)*(a+b*ArcCos[c*x])^n)/Sqrt[d+e*x^2],x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e] && RationalQ[m,n] && n>0 && m>1 && IntegerQ[m]


Int[x_^m_*(a_.+b_.*ArcSin[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  1/(c^(m+1)*Sqrt[d])*Subst[Int[(a+b*x)^n*Sin[x]^m,x],x,ArcSin[c*x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e] && PositiveQ[d] && PositiveIntegerQ[n] && IntegerQ[m]


Int[x_^m_*(a_.+b_.*ArcCos[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  -1/(c^(m+1)*Sqrt[d])*Subst[Int[(a+b*x)^n*Cos[x]^m,x],x,ArcCos[c*x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e] && PositiveQ[d] && PositiveIntegerQ[n] && IntegerQ[m]


Int[(f_.*x_)^m_*(a_.+b_.*ArcSin[c_.*x_])/Sqrt[d_+e_.*x_^2],x_Symbol] :=
  (f*x)^(m+1)*(a+b*ArcSin[c*x])*Hypergeometric2F1[1/2,(1+m)/2,(3+m)/2,c^2*x^2]/(Sqrt[d]*f*(m+1)) - 
  b*c*(f*x)^(m+2)*HypergeometricPFQ[{1,1+m/2,1+m/2},{3/2+m/2,2+m/2},c^2*x^2]/(Sqrt[d]*f^2*(m+1)*(m+2)) /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e] && PositiveQ[d] && Not[IntegerQ[m]]


Int[(f_.*x_)^m_*(a_.+b_.*ArcCos[c_.*x_])/Sqrt[d_+e_.*x_^2],x_Symbol] :=
  (f*x)^(m+1)*(a+b*ArcCos[c*x])*Hypergeometric2F1[1/2,(1+m)/2,(3+m)/2,c^2*x^2]/(Sqrt[d]*f*(m+1)) + 
  b*c*(f*x)^(m+2)*HypergeometricPFQ[{1,1+m/2,1+m/2},{3/2+m/2,2+m/2},c^2*x^2]/(Sqrt[d]*f^2*(m+1)*(m+2)) /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e] && PositiveQ[d] && Not[IntegerQ[m]]


Int[(f_.*x_)^m_*(a_.+b_.*ArcSin[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]*Int[(f*x)^m*(a+b*ArcSin[c*x])^n/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e] && RationalQ[n] && n>0 && Not[PositiveQ[d]] && (IntegerQ[m] || n==1)


Int[(f_.*x_)^m_*(a_.+b_.*ArcCos[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]*Int[(f*x)^m*(a+b*ArcCos[c*x])^n/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e] && RationalQ[n] && n>0 && Not[PositiveQ[d]] && (IntegerQ[m] || n==1)


(* Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  f*(f*x)^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n/(e*(m+2*p+1)) + 
  f^2*(m-1)/(c^2*(m+2*p+1))*Int[(f*x)^(m-2)*(d+e*x^2)^p*(a+b*ArcSin[c*x])^n,x] + 
  b*f*n*d^p/(c*(m+2*p+1))*Int[(f*x)^(m-1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,p},x] && EqQ[c^2*d+e] && RationalQ[m,n] && n>0 && m>1 && NeQ[m+2*p+1] && 
  (IntegerQ[p] || PositiveQ[d]) && IntegerQ[m] *)


(* Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  f*(f*x)^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n/(e*(m+2*p+1)) + 
  f^2*(m-1)/(c^2*(m+2*p+1))*Int[(f*x)^(m-2)*(d+e*x^2)^p*(a+b*ArcCos[c*x])^n,x] - 
  b*f*n*d^p/(c*(m+2*p+1))*Int[(f*x)^(m-1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,p},x] && EqQ[c^2*d+e] && RationalQ[m,n] && n>0 && m>1 && NeQ[m+2*p+1] && 
  (IntegerQ[p] || PositiveQ[d]) && IntegerQ[m] *)


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  f*(f*x)^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n/(e*(m+2*p+1)) + 
  f^2*(m-1)/(c^2*(m+2*p+1))*Int[(f*x)^(m-2)*(d+e*x^2)^p*(a+b*ArcSin[c*x])^n,x] + 
  b*f*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(c*(m+2*p+1)*(1-c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m-1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,p},x] && EqQ[c^2*d+e] && RationalQ[m,n] && n>0 && m>1 && NeQ[m+2*p+1] && IntegerQ[m]


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  f*(f*x)^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n/(e*(m+2*p+1)) + 
  f^2*(m-1)/(c^2*(m+2*p+1))*Int[(f*x)^(m-2)*(d+e*x^2)^p*(a+b*ArcCos[c*x])^n,x] - 
  b*f*n*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(c*(m+2*p+1)*(1-c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m-1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,p},x] && EqQ[c^2*d+e] && RationalQ[m,n] && n>0 && m>1 && NeQ[m+2*p+1] && IntegerQ[m]


(* Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
  (f*x)^m*Sqrt[1-c^2*x^2]*(d+e*x^2)^p*(a+b*ArcSin[c*x])^(n+1)/(b*c*(n+1)) - 
  f*m*d^p/(b*c*(n+1))*Int[(f*x)^(m-1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcSin[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && EqQ[c^2*d+e] && RationalQ[n] && n<-1 && EqQ[m+2*p+1] && (IntegerQ[p] || PositiveQ[d]) *)


(* Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
  -(f*x)^m*Sqrt[1-c^2*x^2]*(d+e*x^2)^p*(a+b*ArcCos[c*x])^(n+1)/(b*c*(n+1)) + 
  f*m*d^p/(b*c*(n+1))*Int[(f*x)^(m-1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcCos[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && EqQ[c^2*d+e] && RationalQ[n] && n<-1 && EqQ[m+2*p+1] && (IntegerQ[p] || PositiveQ[d]) *)


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
  (f*x)^m*Sqrt[1-c^2*x^2]*(d+e*x^2)^p*(a+b*ArcSin[c*x])^(n+1)/(b*c*(n+1)) - 
  f*m*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(b*c*(n+1)*(1-c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m-1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcSin[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && EqQ[c^2*d+e] && RationalQ[n] && n<-1 && EqQ[m+2*p+1]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
  -(f*x)^m*Sqrt[1-c^2*x^2]*(d+e*x^2)^p*(a+b*ArcCos[c*x])^(n+1)/(b*c*(n+1)) + 
  f*m*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(b*c*(n+1)*(1-c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m-1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcCos[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && EqQ[c^2*d+e] && RationalQ[n] && n<-1 && EqQ[m+2*p+1]


Int[(f_.*x_)^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_/Sqrt[d_+e_.*x_^2],x_Symbol] :=
  (f*x)^m*(a+b*ArcSin[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) - 
  f*m/(b*c*Sqrt[d]*(n+1))*Int[(f*x)^(m-1)*(a+b*ArcSin[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e] && RationalQ[n] && n<-1 && PositiveQ[d]


Int[(f_.*x_)^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_/Sqrt[d_+e_.*x_^2],x_Symbol] :=
  -(f*x)^m*(a+b*ArcCos[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) + 
  f*m/(b*c*Sqrt[d]*(n+1))*Int[(f*x)^(m-1)*(a+b*ArcCos[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e] && RationalQ[n] && n<-1 && PositiveQ[d]


(* Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
  (f*x)^m*Sqrt[1-c^2*x^2]*(d+e*x^2)^p*(a+b*ArcSin[c*x])^(n+1)/(b*c*(n+1)) - 
  f*m*d^p/(b*c*(n+1))*Int[(f*x)^(m-1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcSin[c*x])^(n+1),x] + 
  c*(m+2*p+1)*d^p/(b*f*(n+1))*Int[(f*x)^(m+1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcSin[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e] && RationalQ[n] && n<-1 && IntegerQ[m] && m>-3 && PositiveIntegerQ[2*p] && 
  (IntegerQ[p] || PositiveQ[d]) *)


(* Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
  -(f*x)^m*Sqrt[1-c^2*x^2]*(d+e*x^2)^p*(a+b*ArcCos[c*x])^(n+1)/(b*c*(n+1)) + 
  f*m*d^p/(b*c*(n+1))*Int[(f*x)^(m-1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcCos[c*x])^(n+1),x] - 
  c*(m+2*p+1)*d^p/(b*f*(n+1))*Int[(f*x)^(m+1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcCos[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e] && RationalQ[n] && n<-1 && IntegerQ[m] && m>-3 && PositiveIntegerQ[2*p] && 
  (IntegerQ[p] || PositiveQ[d]) *)


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
  (f*x)^m*Sqrt[1-c^2*x^2]*(d+e*x^2)^p*(a+b*ArcSin[c*x])^(n+1)/(b*c*(n+1)) - 
  f*m*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(b*c*(n+1)*(1-c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m-1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcSin[c*x])^(n+1),x] + 
  c*(m+2*p+1)*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(b*f*(n+1)*(1-c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m+1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcSin[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e] && RationalQ[n] && n<-1 && IntegerQ[m] && m>-3 && PositiveIntegerQ[2*p]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
  -(f*x)^m*Sqrt[1-c^2*x^2]*(d+e*x^2)^p*(a+b*ArcCos[c*x])^(n+1)/(b*c*(n+1)) + 
  f*m*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(b*c*(n+1)*(1-c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m-1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcCos[c*x])^(n+1),x] - 
  c*(m+2*p+1)*d^IntPart[p]*(d+e*x^2)^FracPart[p]/(b*f*(n+1)*(1-c^2*x^2)^FracPart[p])*
    Int[(f*x)^(m+1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcCos[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e] && RationalQ[n] && n<-1 && IntegerQ[m] && m>-3 && PositiveIntegerQ[2*p]


Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  d^p/c^(m+1)*Subst[Int[(a+b*x)^n*Sin[x]^m*Cos[x]^(2*p+1),x],x,ArcSin[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e] && IntegerQ[2*p] && p>-1 && PositiveIntegerQ[m] && (IntegerQ[p] || PositiveQ[d])


Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  -d^p/c^(m+1)*Subst[Int[(a+b*x)^n*Cos[x]^m*Sin[x]^(2*p+1),x],x,ArcCos[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e] && IntegerQ[2*p] && p>-1 && PositiveIntegerQ[m] && (IntegerQ[p] || PositiveQ[d])


Int[x_^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
  d^IntPart[p]*(d+e*x^2)^FracPart[p]/(1-c^2*x^2)^FracPart[p]*Int[x^m*(1-c^2*x^2)^p*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e] && IntegerQ[2*p] && p>-1 && PositiveIntegerQ[m] && Not[(IntegerQ[p] || PositiveQ[d])]


Int[x_^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
  d^IntPart[p]*(d+e*x^2)^FracPart[p]/(1-c^2*x^2)^FracPart[p]*Int[x^m*(1-c^2*x^2)^p*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e] && IntegerQ[2*p] && p>-1 && PositiveIntegerQ[m] && Not[(IntegerQ[p] || PositiveQ[d])]


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcSin[c*x])^n/Sqrt[d+e*x^2],(f*x)^m*(d+e*x^2)^(p+1/2),x],x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && EqQ[c^2*d+e] && PositiveQ[d] && PositiveIntegerQ[p+1/2] && Not[PositiveIntegerQ[(m+1)/2]] && 
  IntegerQ[m] && -3<m<0


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcCos[c*x])^n/Sqrt[d+e*x^2],(f*x)^m*(d+e*x^2)^(p+1/2),x],x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && EqQ[c^2*d+e] && PositiveQ[d] && PositiveIntegerQ[p+1/2] && Not[PositiveIntegerQ[(m+1)/2]] && 
  IntegerQ[m] && -3<m<0


Int[x_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_]),x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])/(2*e*(p+1)) - b*c/(2*e*(p+1))*Int[(d+e*x^2)^(p+1)/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c,d,e,p},x] && NeQ[c^2*d+e] && NeQ[p+1]


Int[x_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_]),x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])/(2*e*(p+1)) + b*c/(2*e*(p+1))*Int[(d+e*x^2)^(p+1)/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c,d,e,p},x] && NeQ[c^2*d+e] && NeQ[p+1]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(f*x)^m*(d+e*x^2)^p,x]},  
  Dist[a+b*ArcSin[c*x],u,x] - b*c*Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e,f,m},x] && NeQ[c^2*d+e] && IntegerQ[p] && (p>0 || PositiveIntegerQ[(m-1)/2] && m+p<=0)


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(f*x)^m*(d+e*x^2)^p,x]},  
  Dist[a+b*ArcCos[c*x],u,x] + b*c*Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e,f,m},x] && NeQ[c^2*d+e] && IntegerQ[p] && (p>0 || PositiveIntegerQ[(m-1)/2] && m+p<=0)


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcSin[c*x])^n,(f*x)^m*(d+e*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[c^2*d+e] && PositiveIntegerQ[n] && IntegerQ[p] && IntegerQ[m]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcCos[c*x])^n,(f*x)^m*(d+e*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[c^2*d+e] && PositiveIntegerQ[n] && IntegerQ[p] && IntegerQ[m]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(f*x)^m*(d+e*x^2)^p*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(f*x)^m*(d+e*x^2)^p*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x]


Int[(h_.*x_)^m_.*(d_+e_.*x_)^p_*(f_+g_.*x_)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  (d+e*x)^FracPart[p]*(f+g*x)^FracPart[p]/(d*f+e*g*x^2)^FracPart[p]*
    Int[(h*x)^m*(d*f+e*g*x^2)^p*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n,p},x] && EqQ[e*f+d*g] && EqQ[c^2*f^2-g^2] && Not[IntegerQ[p]]


Int[(h_.*x_)^m_.*(d_+e_.*x_)^p_*(f_+g_.*x_)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  (d+e*x)^FracPart[p]*(f+g*x)^FracPart[p]/(d*f+e*g*x^2)^FracPart[p]*
    Int[(h*x)^m*(d*f+e*g*x^2)^p*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n,p},x] && EqQ[e*f+d*g] && EqQ[c^2*f^2-g^2] && Not[IntegerQ[p]]





(* ::Subsection::Closed:: *)
(*5.1.5 u (a+b arcsin(c x))^n*)


Int[(a_.+b_.*ArcSin[c_.*x_])^n_./(d_+e_.*x_),x_Symbol] :=
  Subst[Int[(a+b*x)^n*Cos[x]/(c*d+e*Sin[x]),x],x,ArcSin[c*x]] /;
FreeQ[{a,b,c,d,e},x] && PositiveIntegerQ[n]


Int[(a_.+b_.*ArcCos[c_.*x_])^n_./(d_+e_.*x_),x_Symbol] :=
  -Subst[Int[(a+b*x)^n*Sin[x]/(c*d+e*Cos[x]),x],x,ArcCos[c*x]] /;
FreeQ[{a,b,c,d,e},x] && PositiveIntegerQ[n]


Int[(d_+e_.*x_)^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*ArcSin[c*x])^n/(e*(m+1)) - 
  b*c*n/(e*(m+1))*Int[(d+e*x)^(m+1)*(a+b*ArcSin[c*x])^(n-1)/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c,d,e,m},x] && PositiveIntegerQ[n] && NeQ[m+1]


Int[(d_+e_.*x_)^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*ArcCos[c*x])^n/(e*(m+1)) + 
  b*c*n/(e*(m+1))*Int[(d+e*x)^(m+1)*(a+b*ArcCos[c*x])^(n-1)/Sqrt[1-c^2*x^2],x] /;
FreeQ[{a,b,c,d,e,m},x] && PositiveIntegerQ[n] && NeQ[m+1]


Int[(d_+e_.*x_)^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(a+b*ArcSin[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e},x] && PositiveIntegerQ[m] && RationalQ[n] && n<-1


Int[(d_+e_.*x_)^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(a+b*ArcCos[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e},x] && PositiveIntegerQ[m] && RationalQ[n] && n<-1


Int[(d_.+e_.*x_)^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
  1/c^(m+1)*Subst[Int[(a+b*x)^n*Cos[x]*(c*d+e*Sin[x])^m,x],x,ArcSin[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && PositiveIntegerQ[m]


Int[(d_.+e_.*x_)^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
  -1/c^(m+1)*Subst[Int[(a+b*x)^n*Sin[x]*(c*d+e*Cos[x])^m,x],x,ArcCos[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && PositiveIntegerQ[m]


Int[Px_*(a_.+b_.*ArcSin[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[ExpandExpression[Px,x],x]},  
  Dist[a+b*ArcSin[c*x],u,x] - b*c*Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c},x] && PolynomialQ[Px,x]


Int[Px_*(a_.+b_.*ArcCos[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[ExpandExpression[Px,x],x]},  
  Dist[a+b*ArcCos[c*x],u,x] + b*c*Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c},x] && PolynomialQ[Px,x]


(* Int[Px_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  With[{u=IntHide[Px,x]},  
  Dist[(a+b*ArcSin[c*x])^n,u,x] - b*c*n*Int[SimplifyIntegrand[u*(a+b*ArcSin[c*x])^(n-1)/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c},x] && PolynomialQ[Px,x] && PositiveIntegerQ[n] *)


(* Int[Px_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  With[{u=IntHide[Px,x]},  
  Dist[(a+b*ArcCos[c*x])^n,u,x] + b*c*n*Int[SimplifyIntegrand[u*(a+b*ArcCos[c*x])^(n-1)/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c},x] && PolynomialQ[Px,x] && PositiveIntegerQ[n] *)


Int[Px_*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
  Int[ExpandIntegrand[Px*(a+b*ArcSin[c*x])^n,x],x] /;
FreeQ[{a,b,c,n},x] && PolynomialQ[Px,x]


Int[Px_*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
  Int[ExpandIntegrand[Px*(a+b*ArcCos[c*x])^n,x],x] /;
FreeQ[{a,b,c,n},x] && PolynomialQ[Px,x]


Int[Px_*(d_.+e_.*x_)^m_.*(a_.+b_.*ArcSin[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[Px*(d+e*x)^m,x]},  
  Dist[a+b*ArcSin[c*x],u,x] - b*c*Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e,m},x] && PolynomialQ[Px,x]


Int[Px_*(d_.+e_.*x_)^m_.*(a_.+b_.*ArcCos[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[Px*(d+e*x)^m,x]},  
  Dist[a+b*ArcCos[c*x],u,x] + b*c*Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e,m},x] && PolynomialQ[Px,x]


Int[(f_.+g_.*x_)^p_.*(d_+e_.*x_)^m_*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
  With[{u=IntHide[(f+g*x)^p*(d+e*x)^m,x]},  
  Dist[(a+b*ArcSin[c*x])^n,u,x] - b*c*n*Int[SimplifyIntegrand[u*(a+b*ArcSin[c*x])^(n-1)/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && PositiveIntegerQ[n,p] && NegativeIntegerQ[m] && m+p+1<0


Int[(f_.+g_.*x_)^p_.*(d_+e_.*x_)^m_*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
  With[{u=IntHide[(f+g*x)^p*(d+e*x)^m,x]},  
  Dist[(a+b*ArcCos[c*x])^n,u,x] + b*c*n*Int[SimplifyIntegrand[u*(a+b*ArcCos[c*x])^(n-1)/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && PositiveIntegerQ[n,p] && NegativeIntegerQ[m] && m+p+1<0


Int[(f_.+g_.*x_+h_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_/(d_+e_.*x_)^2,x_Symbol] :=
  With[{u=IntHide[(f+g*x+h*x^2)^p/(d+e*x)^2,x]},  
  Dist[(a+b*ArcSin[c*x])^n,u,x] - b*c*n*Int[SimplifyIntegrand[u*(a+b*ArcSin[c*x])^(n-1)/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e,f,g,h},x] && PositiveIntegerQ[n,p] && EqQ[e*g-2*d*h]


Int[(f_.+g_.*x_+h_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_/(d_+e_.*x_)^2,x_Symbol] :=
  With[{u=IntHide[(f+g*x+h*x^2)^p/(d+e*x)^2,x]},  
  Dist[(a+b*ArcCos[c*x])^n,u,x] + b*c*n*Int[SimplifyIntegrand[u*(a+b*ArcCos[c*x])^(n-1)/Sqrt[1-c^2*x^2],x],x]] /;
FreeQ[{a,b,c,d,e,f,g,h},x] && PositiveIntegerQ[n,p] && EqQ[e*g-2*d*h]


Int[Px_*(d_+e_.*x_)^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
  Int[ExpandIntegrand[Px*(d+e*x)^m*(a+b*ArcSin[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e},x] && PolynomialQ[Px,x] && PositiveIntegerQ[n] && IntegerQ[m]


Int[Px_*(d_+e_.*x_)^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
  Int[ExpandIntegrand[Px*(d+e*x)^m*(a+b*ArcCos[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e},x] && PolynomialQ[Px,x] && PositiveIntegerQ[n] && IntegerQ[m]


Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(f+g*x)^m*(d+e*x^2)^p,x]},  
  Dist[a+b*ArcSin[c*x],u,x] - b*c*Int[Dist[1/Sqrt[1-c^2*x^2],u,x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c^2*d+e] && IntegerQ[m] && NegativeIntegerQ[p+1/2] && PositiveQ[d] && m>0 && 
  (m<-2*p-1 || m>3)


Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(f+g*x)^m*(d+e*x^2)^p,x]},  
  Dist[a+b*ArcCos[c*x],u,x] + b*c*Int[Dist[1/Sqrt[1-c^2*x^2],u,x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c^2*d+e] && IntegerQ[m] && NegativeIntegerQ[p+1/2] && PositiveQ[d] && m>0 && 
  (m<-2*p-1 || m>3)


Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^2)^p*(a+b*ArcSin[c*x])^n,(f+g*x)^m,x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c^2*d+e] && IntegerQ[m] && IntegerQ[p+1/2] && PositiveQ[d] && PositiveIntegerQ[n] && m>0 && 
  (n==1 && p>-1 || p>0 || m==1 || m==2 && p<-2)


Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^2)^p*(a+b*ArcCos[c*x])^n,(f+g*x)^m,x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c^2*d+e] && IntegerQ[m] && IntegerQ[p+1/2] && PositiveQ[d] && PositiveIntegerQ[n] && m>0 && 
  (n==1 && p>-1 || p>0 || m==1 || m==2 && p<-2)


Int[(f_+g_.*x_)^m_*Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  (f+g*x)^m*(d+e*x^2)*(a+b*ArcSin[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) - 
  1/(b*c*Sqrt[d]*(n+1))*Int[(d*g*m+2*e*f*x+e*g*(m+2)*x^2)*(f+g*x)^(m-1)*(a+b*ArcSin[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c^2*d+e] && IntegerQ[m] && PositiveQ[d] && PositiveIntegerQ[n] && m<0


Int[(f_+g_.*x_)^m_*Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  -(f+g*x)^m*(d+e*x^2)*(a+b*ArcCos[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) + 
  1/(b*c*Sqrt[d]*(n+1))*Int[(d*g*m+2*e*f*x+e*g*(m+2)*x^2)*(f+g*x)^(m-1)*(a+b*ArcCos[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c^2*d+e] && IntegerQ[m] && PositiveQ[d] && PositiveIntegerQ[n] && m<0


Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[Sqrt[d+e*x^2]*(a+b*ArcSin[c*x])^n,(f+g*x)^m*(d+e*x^2)^(p-1/2),x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c^2*d+e] && IntegerQ[m] && PositiveIntegerQ[p+1/2] && PositiveQ[d] && PositiveIntegerQ[n]


Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[Sqrt[d+e*x^2]*(a+b*ArcCos[c*x])^n,(f+g*x)^m*(d+e*x^2)^(p-1/2),x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c^2*d+e] && IntegerQ[m] && PositiveIntegerQ[p+1/2] && PositiveQ[d] && PositiveIntegerQ[n]


Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  (f+g*x)^m*(d+e*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) - 
  1/(b*c*Sqrt[d]*(n+1))*
    Int[ExpandIntegrand[(f+g*x)^(m-1)*(a+b*ArcSin[c*x])^(n+1),(d*g*m+e*f*(2*p+1)*x+e*g*(m+2*p+1)*x^2)*(d+e*x^2)^(p-1/2),x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c^2*d+e] && IntegerQ[m] && PositiveIntegerQ[p-1/2] && PositiveQ[d] && PositiveIntegerQ[n] && m<0


Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  -(f+g*x)^m*(d+e*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) + 
  1/(b*c*Sqrt[d]*(n+1))*
    Int[ExpandIntegrand[(f+g*x)^(m-1)*(a+b*ArcCos[c*x])^(n+1),(d*g*m+e*f*(2*p+1)*x+e*g*(m+2*p+1)*x^2)*(d+e*x^2)^(p-1/2),x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c^2*d+e] && IntegerQ[m] && PositiveIntegerQ[p-1/2] && PositiveQ[d] && PositiveIntegerQ[n] && m<0


Int[(f_+g_.*x_)^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_/Sqrt[d_+e_.*x_^2],x_Symbol] :=
  (f+g*x)^m*(a+b*ArcSin[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) - 
  g*m/(b*c*Sqrt[d]*(n+1))*Int[(f+g*x)^(m-1)*(a+b*ArcSin[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c^2*d+e] && IntegerQ[m] && PositiveQ[d] && m>0 && RationalQ[n] && n<-1


Int[(f_+g_.*x_)^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_/Sqrt[d_+e_.*x_^2],x_Symbol] :=
  -(f+g*x)^m*(a+b*ArcCos[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) + 
  g*m/(b*c*Sqrt[d]*(n+1))*Int[(f+g*x)^(m-1)*(a+b*ArcCos[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c^2*d+e] && IntegerQ[m] && PositiveQ[d] && m>0 && RationalQ[n] && n<-1


Int[(f_+g_.*x_)^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  1/(c^(m+1)*Sqrt[d])*Subst[Int[(a+b*x)^n*(c*f+g*Sin[x])^m,x],x,ArcSin[c*x]] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && EqQ[c^2*d+e] && IntegerQ[m] && PositiveQ[d] && (m>0 || PositiveIntegerQ[n])


Int[(f_+g_.*x_)^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  -1/(c^(m+1)*Sqrt[d])*Subst[Int[(a+b*x)^n*(c*f+g*Cos[x])^m,x],x,ArcCos[c*x]] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && EqQ[c^2*d+e] && IntegerQ[m] && PositiveQ[d] && (m>0 || PositiveIntegerQ[n])


Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcSin[c*x])^n/Sqrt[d+e*x^2],(f+g*x)^m*(d+e*x^2)^(p+1/2),x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c^2*d+e] && IntegerQ[m] && NegativeIntegerQ[p+1/2] && PositiveQ[d] && PositiveIntegerQ[n]


Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcCos[c*x])^n/Sqrt[d+e*x^2],(f+g*x)^m*(d+e*x^2)^(p+1/2),x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c^2*d+e] && IntegerQ[m] && NegativeIntegerQ[p+1/2] && PositiveQ[d] && PositiveIntegerQ[n]


Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  d^IntPart[p]*(d+e*x^2)^FracPart[p]/(1-c^2*x^2)^FracPart[p]*Int[(f+g*x)^m*(1-c^2*x^2)^p*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && EqQ[c^2*d+e] && IntegerQ[m] && IntegerQ[p-1/2] && Not[PositiveQ[d]]


Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  d^IntPart[p]*(d+e*x^2)^FracPart[p]/(1-c^2*x^2)^FracPart[p]*Int[(f+g*x)^m*(1-c^2*x^2)^p*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && EqQ[c^2*d+e] && IntegerQ[m] && IntegerQ[p-1/2] && Not[PositiveQ[d]]


Int[Log[h_.*(f_.+g_.*x_)^m_.]*(a_.+b_.*ArcSin[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  Log[h*(f+g*x)^m]*(a+b*ArcSin[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) - 
  g*m/(b*c*Sqrt[d]*(n+1))*Int[(a+b*ArcSin[c*x])^(n+1)/(f+g*x),x] /;
FreeQ[{a,b,c,d,e,f,g,h,m},x] && EqQ[c^2*d+e] && PositiveQ[d] && PositiveIntegerQ[n]


Int[Log[h_.*(f_.+g_.*x_)^m_.]*(a_.+b_.*ArcCos[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  -Log[h*(f+g*x)^m]*(a+b*ArcCos[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) + 
  g*m/(b*c*Sqrt[d]*(n+1))*Int[(a+b*ArcCos[c*x])^(n+1)/(f+g*x),x] /;
FreeQ[{a,b,c,d,e,f,g,h,m},x] && EqQ[c^2*d+e] && PositiveQ[d] && PositiveIntegerQ[n]


Int[Log[h_.*(f_.+g_.*x_)^m_.]*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  d^IntPart[p]*(d+e*x^2)^FracPart[p]/(1-c^2*x^2)^FracPart[p]*Int[Log[h*(f+g*x)^m]*(1-c^2*x^2)^p*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n},x] && EqQ[c^2*d+e] && IntegerQ[p-1/2] && Not[PositiveQ[d]]


Int[Log[h_.*(f_.+g_.*x_)^m_.]*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  d^IntPart[p]*(d+e*x^2)^FracPart[p]/(1-c^2*x^2)^FracPart[p]*Int[Log[h*(f+g*x)^m]*(1-c^2*x^2)^p*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n},x] && EqQ[c^2*d+e] && IntegerQ[p-1/2] && Not[PositiveQ[d]]


Int[(d_+e_.*x_)^m_*(f_+g_.*x_)^m_*(a_.+b_.*ArcSin[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(d+e*x)^m*(f+g*x)^m,x]},  
  Dist[a+b*ArcSin[c*x],u,x] - b*c*Int[Dist[1/Sqrt[1-c^2*x^2],u,x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && NegativeIntegerQ[m+1/2]


Int[(d_+e_.*x_)^m_*(f_+g_.*x_)^m_*(a_.+b_.*ArcCos[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(d+e*x)^m*(f+g*x)^m,x]},  
  Dist[a+b*ArcCos[c*x],u,x] + b*c*Int[Dist[1/Sqrt[1-c^2*x^2],u,x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && NegativeIntegerQ[m+1/2]


Int[(d_+e_.*x_)^m_.*(f_+g_.*x_)^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)^m*(a+b*ArcSin[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && IntegerQ[m]


Int[(d_+e_.*x_)^m_.*(f_+g_.*x_)^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)^m*(a+b*ArcCos[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && IntegerQ[m]


Int[u_*(a_.+b_.*ArcSin[c_.*x_]),x_Symbol] :=
  With[{v=IntHide[u,x]},  
  Dist[a+b*ArcSin[c*x],v,x] - b*c*Int[SimplifyIntegrand[v/Sqrt[1-c^2*x^2],x],x] /;
 InverseFunctionFreeQ[v,x]] /;
FreeQ[{a,b,c},x]


Int[u_*(a_.+b_.*ArcCos[c_.*x_]),x_Symbol] :=
  With[{v=IntHide[u,x]},  
  Dist[a+b*ArcCos[c*x],v,x] + b*c*Int[SimplifyIntegrand[v/Sqrt[1-c^2*x^2],x],x] /;
 InverseFunctionFreeQ[v,x]] /;
FreeQ[{a,b,c},x]


Int[Px_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  With[{u=ExpandIntegrand[Px*(d+e*x^2)^p*(a+b*ArcSin[c*x])^n,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{a,b,c,d,e,n},x] && PolynomialQ[Px,x] && EqQ[c^2*d+e] && IntegerQ[p-1/2]


Int[Px_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  With[{u=ExpandIntegrand[Px*(d+e*x^2)^p*(a+b*ArcCos[c*x])^n,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{a,b,c,d,e,n},x] && PolynomialQ[Px,x] && EqQ[c^2*d+e] && IntegerQ[p-1/2]


Int[Px_.*(f_+g_.*(d_+e_.*x_^2)^p_)^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  With[{u=ExpandIntegrand[Px*(f+g*(d+e*x^2)^p)^m*(a+b*ArcSin[c*x])^n,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{a,b,c,d,e,f,g},x] && PolynomialQ[Px,x] && EqQ[c^2*d+e] && PositiveIntegerQ[p+1/2] && IntegersQ[m,n]


Int[Px_.*(f_+g_.*(d_+e_.*x_^2)^p_)^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  With[{u=ExpandIntegrand[Px*(f+g*(d+e*x^2)^p)^m*(a+b*ArcCos[c*x])^n,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{a,b,c,d,e,f,g},x] && PolynomialQ[Px,x] && EqQ[c^2*d+e] && PositiveIntegerQ[p+1/2] && IntegersQ[m,n]


Int[RFx_*ArcSin[c_.*x_]^n_.,x_Symbol] :=
  With[{u=ExpandIntegrand[ArcSin[c*x]^n,RFx,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[c,x] && RationalFunctionQ[RFx,x] && PositiveIntegerQ[n]


Int[RFx_*ArcCos[c_.*x_]^n_.,x_Symbol] :=
  With[{u=ExpandIntegrand[ArcCos[c*x]^n,RFx,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[c,x] && RationalFunctionQ[RFx,x] && PositiveIntegerQ[n]


Int[RFx_*(a_+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[RFx*(a+b*ArcSin[c*x])^n,x],x] /;
FreeQ[{a,b,c},x] && RationalFunctionQ[RFx,x] && PositiveIntegerQ[n]


Int[RFx_*(a_+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[RFx*(a+b*ArcCos[c*x])^n,x],x] /;
FreeQ[{a,b,c},x] && RationalFunctionQ[RFx,x] && PositiveIntegerQ[n]


Int[RFx_*(d_+e_.*x_^2)^p_*ArcSin[c_.*x_]^n_.,x_Symbol] :=
  With[{u=ExpandIntegrand[(d+e*x^2)^p*ArcSin[c*x]^n,RFx,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{c,d,e},x] && RationalFunctionQ[RFx,x] && PositiveIntegerQ[n] && EqQ[c^2*d+e] && IntegerQ[p-1/2]


Int[RFx_*(d_+e_.*x_^2)^p_*ArcCos[c_.*x_]^n_.,x_Symbol] :=
  With[{u=ExpandIntegrand[(d+e*x^2)^p*ArcCos[c*x]^n,RFx,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{c,d,e},x] && RationalFunctionQ[RFx,x] && PositiveIntegerQ[n] && EqQ[c^2*d+e] && IntegerQ[p-1/2]


Int[RFx_*(d_+e_.*x_^2)^p_*(a_+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^2)^p,RFx*(a+b*ArcSin[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e},x] && RationalFunctionQ[RFx,x] && PositiveIntegerQ[n] && EqQ[c^2*d+e] && IntegerQ[p-1/2]


Int[RFx_*(d_+e_.*x_^2)^p_*(a_+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^2)^p,RFx*(a+b*ArcCos[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e},x] && RationalFunctionQ[RFx,x] && PositiveIntegerQ[n] && EqQ[c^2*d+e] && IntegerQ[p-1/2]


Int[u_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][u*(a+b*ArcSin[c*x])^n,x] /;
FreeQ[{a,b,c,n},x]


Int[u_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][u*(a+b*ArcCos[c*x])^n,x] /;
FreeQ[{a,b,c,n},x]





(* ::Subsection::Closed:: *)
(*5.1.6 Miscellaneous inverse sine*)
(**)


Int[(a_.+b_.*ArcSin[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[(a+b*ArcSin[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,n},x]


Int[(a_.+b_.*ArcCos[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[(a+b*ArcCos[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,n},x]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcSin[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[((d*e-c*f)/d+f*x/d)^m*(a+b*ArcSin[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,m,n},x]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCos[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[((d*e-c*f)/d+f*x/d)^m*(a+b*ArcCos[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,m,n},x]


Int[(A_.+B_.*x_+C_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[(-C/d^2+C/d^2*x^2)^p*(a+b*ArcSin[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,A,B,C,n,p},x] && EqQ[B*(1-c^2)+2*A*c*d] && EqQ[2*c*C-B*d]


Int[(A_.+B_.*x_+C_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[(-C/d^2+C/d^2*x^2)^p*(a+b*ArcCos[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,A,B,C,n,p},x] && EqQ[B*(1-c^2)+2*A*c*d] && EqQ[2*c*C-B*d]


Int[(e_.+f_.*x_)^m_.*(A_.+B_.*x_+C_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[((d*e-c*f)/d+f*x/d)^m*(-C/d^2+C/d^2*x^2)^p*(a+b*ArcSin[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m,n,p},x] && EqQ[B*(1-c^2)+2*A*c*d] && EqQ[2*c*C-B*d]


Int[(e_.+f_.*x_)^m_.*(A_.+B_.*x_+C_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[((d*e-c*f)/d+f*x/d)^m*(-C/d^2+C/d^2*x^2)^p*(a+b*ArcCos[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m,n,p},x] && EqQ[B*(1-c^2)+2*A*c*d] && EqQ[2*c*C-B*d]


Int[Sqrt[a_.+b_.*ArcSin[c_+d_.*x_^2]],x_Symbol] :=
  x*Sqrt[a+b*ArcSin[c+d*x^2]] - 
  Sqrt[Pi]*x*(Cos[a/(2*b)]+c*Sin[a/(2*b)])*FresnelC[Sqrt[c/(Pi*b)]*Sqrt[a+b*ArcSin[c+d*x^2]]]/
    (Sqrt[c/b]*(Cos[ArcSin[c+d*x^2]/2]-c*Sin[ArcSin[c+d*x^2]/2])) + 
  Sqrt[Pi]*x*(Cos[a/(2*b)]-c*Sin[a/(2*b)])*FresnelS[Sqrt[c/(Pi*b)]*Sqrt[a+b*ArcSin[c+d*x^2]]]/
    (Sqrt[c/b]*(Cos[ArcSin[c+d*x^2]/2]-c*Sin[ArcSin[c+d*x^2]/2])) /;
FreeQ[{a,b,c,d},x] && EqQ[c^2-1]


Int[Sqrt[a_.+b_.*ArcCos[1+d_.*x_^2]],x_Symbol] :=
  -2*Sqrt[a+b*ArcCos[1+d*x^2]]*Sin[ArcCos[1+d*x^2]/2]^2/(d*x) - 
  2*Sqrt[Pi]*Sin[a/(2*b)]*Sin[ArcCos[1+d*x^2]/2]*FresnelC[Sqrt[1/(Pi*b)]*Sqrt[a+b*ArcCos[1+d*x^2]]]/(Sqrt[1/b]*d*x) + 
  2*Sqrt[Pi]*Cos[a/(2*b)]*Sin[ArcCos[1+d*x^2]/2]*FresnelS[Sqrt[1/(Pi*b)]*Sqrt[a+b*ArcCos[1+d*x^2]]]/(Sqrt[1/b]*d*x) /;
FreeQ[{a,b,d},x]


Int[Sqrt[a_.+b_.*ArcCos[-1+d_.*x_^2]],x_Symbol] :=
  2*Sqrt[a+b*ArcCos[-1+d*x^2]]*Cos[(1/2)*ArcCos[-1+d*x^2]]^2/(d*x) - 
  2*Sqrt[Pi]*Cos[a/(2*b)]*Cos[ArcCos[-1+d*x^2]/2]*FresnelC[Sqrt[1/(Pi*b)]*Sqrt[a+b*ArcCos[-1+d*x^2]]]/(Sqrt[1/b]*d*x) - 
  2*Sqrt[Pi]*Sin[a/(2*b)]*Cos[ArcCos[-1+d*x^2]/2]*FresnelS[Sqrt[1/(Pi*b)]*Sqrt[a+b*ArcCos[-1+d*x^2]]]/(Sqrt[1/b]*d*x) /;
FreeQ[{a,b,d},x]


Int[(a_.+b_.*ArcSin[c_+d_.*x_^2])^n_,x_Symbol] :=
  x*(a+b*ArcSin[c+d*x^2])^n + 
  2*b*n*Sqrt[-2*c*d*x^2-d^2*x^4]*(a+b*ArcSin[c+d*x^2])^(n-1)/(d*x) - 
  4*b^2*n*(n-1)*Int[(a+b*ArcSin[c+d*x^2])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && EqQ[c^2-1] && RationalQ[n] && n>1


Int[(a_.+b_.*ArcCos[c_+d_.*x_^2])^n_,x_Symbol] :=
  x*(a+b*ArcCos[c+d*x^2])^n - 
  2*b*n*Sqrt[-2*c*d*x^2-d^2*x^4]*(a+b*ArcCos[c+d*x^2])^(n-1)/(d*x) - 
  4*b^2*n*(n-1)*Int[(a+b*ArcCos[c+d*x^2])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && EqQ[c^2-1] && RationalQ[n] && n>1


Int[1/(a_.+b_.*ArcSin[c_+d_.*x_^2]),x_Symbol] :=
  -x*(c*Cos[a/(2*b)]-Sin[a/(2*b)])*CosIntegral[(c/(2*b))*(a+b*ArcSin[c+d*x^2])]/
    (2*b*(Cos[ArcSin[c+d*x^2]/2]-c*Sin[ArcSin[c+d*x^2]/2])) - 
  x*(c*Cos[a/(2*b)]+Sin[a/(2*b)])*SinIntegral[(c/(2*b))*(a+b*ArcSin[c+d*x^2])]/
    (2*b*(Cos[ArcSin[c+d*x^2]/2]-c*Sin[ArcSin[c+d*x^2]/2])) /;
FreeQ[{a,b,c,d},x] && EqQ[c^2-1]


Int[1/(a_.+b_.*ArcCos[1+d_.*x_^2]),x_Symbol] :=
  x*Cos[a/(2*b)]*CosIntegral[(a+b*ArcCos[1+d*x^2])/(2*b)]/(Sqrt[2]*b*Sqrt[-d*x^2]) + 
  x*Sin[a/(2*b)]*SinIntegral[(a+b*ArcCos[1+d*x^2])/(2*b)]/(Sqrt[2]*b*Sqrt[-d*x^2]) /;
FreeQ[{a,b,d},x]


Int[1/(a_.+b_.*ArcCos[-1+d_.*x_^2]),x_Symbol] :=
  x*Sin[a/(2*b)]*CosIntegral[(a+b*ArcCos[-1+d*x^2])/(2*b)]/(Sqrt[2]*b*Sqrt[d*x^2]) - 
  x*Cos[a/(2*b)]*SinIntegral[(a+b*ArcCos[-1+d*x^2])/(2*b)]/(Sqrt[2]*b*Sqrt[d*x^2]) /;
FreeQ[{a,b,d},x]


Int[1/Sqrt[a_.+b_.*ArcSin[c_+d_.*x_^2]],x_Symbol] :=
  -Sqrt[Pi]*x*(Cos[a/(2*b)]-c*Sin[a/(2*b)])*FresnelC[1/(Sqrt[b*c]*Sqrt[Pi])*Sqrt[a+b*ArcSin[c+d*x^2]]]/
    (Sqrt[b*c]*(Cos[ArcSin[c+d*x^2]/2]-c*Sin[ArcSin[c+d*x^2]/2])) - 
  Sqrt[Pi]*x*(Cos[a/(2*b)]+c*Sin[a/(2*b)])*FresnelS[(1/(Sqrt[b*c]*Sqrt[Pi]))*Sqrt[a+b*ArcSin[c+d*x^2]]]/
    (Sqrt[b*c]*(Cos[ArcSin[c+d*x^2]/2]-c*Sin[ArcSin[c+d*x^2]/2])) /;
FreeQ[{a,b,c,d},x] && EqQ[c^2-1]


Int[1/Sqrt[a_.+b_.*ArcCos[1+d_.*x_^2]],x_Symbol] :=
  -2*Sqrt[Pi/b]*Cos[a/(2*b)]*Sin[ArcCos[1+d*x^2]/2]*FresnelC[Sqrt[1/(Pi*b)]*Sqrt[a+b*ArcCos[1+d*x^2]]]/(d*x) - 
   2*Sqrt[Pi/b]*Sin[a/(2*b)]*Sin[ArcCos[1+d*x^2]/2]*FresnelS[Sqrt[1/(Pi*b)]*Sqrt[a+b*ArcCos[1+d*x^2]]]/(d*x) /;
FreeQ[{a,b,d},x]


Int[1/Sqrt[a_.+b_.*ArcCos[-1+d_.*x_^2]],x_Symbol] :=
  2*Sqrt[Pi/b]*Sin[a/(2*b)]*Cos[ArcCos[-1+d*x^2]/2]*FresnelC[Sqrt[1/(Pi*b)]*Sqrt[a+b*ArcCos[-1+d*x^2]]]/(d*x) - 
  2*Sqrt[Pi/b]*Cos[a/(2*b)]*Cos[ArcCos[-1+d*x^2]/2]*FresnelS[Sqrt[1/(Pi*b)]*Sqrt[a+b*ArcCos[-1+d*x^2]]]/(d*x) /;
FreeQ[{a,b,d},x]


Int[1/(a_.+b_.*ArcSin[c_+d_.*x_^2])^(3/2),x_Symbol] :=
  -Sqrt[-2*c*d*x^2-d^2*x^4]/(b*d*x*Sqrt[a+b*ArcSin[c+d*x^2]]) - 
  (c/b)^(3/2)*Sqrt[Pi]*x*(Cos[a/(2*b)]+c*Sin[a/(2*b)])*FresnelC[Sqrt[c/(Pi*b)]*Sqrt[a+b*ArcSin[c+d*x^2]]]/
    (Cos[(1/2)*ArcSin[c+d*x^2]]-c*Sin[ArcSin[c+d*x^2]/2]) + 
  (c/b)^(3/2)*Sqrt[Pi]*x*(Cos[a/(2*b)]-c*Sin[a/(2*b)])*FresnelS[Sqrt[c/(Pi*b)]*Sqrt[a+b*ArcSin[c+d*x^2]]]/
    (Cos[(1/2)*ArcSin[c+d*x^2]]-c*Sin[ArcSin[c+d*x^2]/2]) /;
FreeQ[{a,b,c,d},x] && EqQ[c^2-1]


Int[1/(a_.+b_.*ArcCos[1+d_.*x_^2])^(3/2),x_Symbol] :=
  Sqrt[-2*d*x^2-d^2*x^4]/(b*d*x*Sqrt[a+b*ArcCos[1+d*x^2]]) - 
  2*(1/b)^(3/2)*Sqrt[Pi]*Sin[a/(2*b)]*Sin[ArcCos[1+d*x^2]/2]*FresnelC[Sqrt[1/(Pi*b)]*Sqrt[a+b*ArcCos[1+d*x^2]]]/(d*x) + 
  2*(1/b)^(3/2)*Sqrt[Pi]*Cos[a/(2*b)]*Sin[ArcCos[1+d*x^2]/2]*FresnelS[Sqrt[1/(Pi*b)]*Sqrt[a+b*ArcCos[1+d*x^2]]]/(d*x) /;
FreeQ[{a,b,d},x]


Int[1/(a_.+b_.*ArcCos[-1+d_.*x_^2])^(3/2),x_Symbol] :=
  Sqrt[2*d*x^2-d^2*x^4]/(b*d*x*Sqrt[a+b*ArcCos[-1+d*x^2]]) - 
  2*(1/b)^(3/2)*Sqrt[Pi]*Cos[a/(2*b)]*Cos[ArcCos[-1+d*x^2]/2]*FresnelC[Sqrt[1/(Pi*b)]*Sqrt[a+b*ArcCos[-1+d*x^2]]]/(d*x) - 
  2*(1/b)^(3/2)*Sqrt[Pi]*Sin[a/(2*b)]*Cos[ArcCos[-1+d*x^2]/2]*FresnelS[Sqrt[1/(Pi*b)]*Sqrt[a+b*ArcCos[-1+d*x^2]]]/(d*x) /;
FreeQ[{a,b,d},x]


Int[1/(a_.+b_.*ArcSin[c_+d_.*x_^2])^2,x_Symbol] :=
  -Sqrt[-2*c*d*x^2-d^2*x^4]/(2*b*d*x*(a+b*ArcSin[c+d*x^2])) - 
  x*(Cos[a/(2*b)]+c*Sin[a/(2*b)])*CosIntegral[(c/(2*b))*(a+b*ArcSin[c+d*x^2])]/
    (4*b^2*(Cos[ArcSin[c+d*x^2]/2]-c*Sin[ArcSin[c+d*x^2]/2])) + 
  x*(Cos[a/(2*b)]-c*Sin[a/(2*b)])*SinIntegral[(c/(2*b))*(a+b*ArcSin[c+d*x^2])]/
    (4*b^2*(Cos[ArcSin[c+d*x^2]/2]-c*Sin[ArcSin[c+d*x^2]/2])) /;
FreeQ[{a,b,c,d},x] && EqQ[c^2-1]


Int[1/(a_.+b_.*ArcCos[1+d_.*x_^2])^2,x_Symbol] :=
  Sqrt[-2*d*x^2-d^2*x^4]/(2*b*d*x*(a+b*ArcCos[1+d*x^2])) + 
  x*Sin[a/(2*b)]*CosIntegral[(a+b*ArcCos[1+d*x^2])/(2*b)]/(2*Sqrt[2]*b^2*Sqrt[(-d)*x^2]) - 
  x*Cos[a/(2*b)]*SinIntegral[(a+b*ArcCos[1+d*x^2])/(2*b)]/(2*Sqrt[2]*b^2*Sqrt[(-d)*x^2]) /;
FreeQ[{a,b,d},x]


Int[1/(a_.+b_.*ArcCos[-1+d_.*x_^2])^2,x_Symbol] :=
  Sqrt[2*d*x^2-d^2*x^4]/(2*b*d*x*(a+b*ArcCos[-1+d*x^2])) - 
  x*Cos[a/(2*b)]*CosIntegral[(a+b*ArcCos[-1+d*x^2])/(2*b)]/(2*Sqrt[2]*b^2*Sqrt[d*x^2]) - 
  x*Sin[a/(2*b)]*SinIntegral[(a+b*ArcCos[-1+d*x^2])/(2*b)]/(2*Sqrt[2]*b^2*Sqrt[d*x^2]) /;
FreeQ[{a,b,d},x]


Int[(a_.+b_.*ArcSin[c_+d_.*x_^2])^n_,x_Symbol] :=
  x*(a+b*ArcSin[c+d*x^2])^(n+2)/(4*b^2*(n+1)*(n+2)) + 
  Sqrt[-2*c*d*x^2-d^2*x^4]*(a+b*ArcSin[c+d*x^2])^(n+1)/(2*b*d*(n+1)*x) - 
  1/(4*b^2*(n+1)*(n+2))*Int[(a+b*ArcSin[c+d*x^2])^(n+2),x] /;
FreeQ[{a,b,c,d},x] && EqQ[c^2-1] && RationalQ[n] && n<-1 && n!=-2


Int[(a_.+b_.*ArcCos[c_+d_.*x_^2])^n_,x_Symbol] :=
  x*(a+b*ArcCos[c+d*x^2])^(n+2)/(4*b^2*(n+1)*(n+2)) - 
  Sqrt[-2*c*d*x^2-d^2*x^4]*(a+b*ArcCos[c+d*x^2])^(n+1)/(2*b*d*(n+1)*x) - 
  1/(4*b^2*(n+1)*(n+2))*Int[(a+b*ArcCos[c+d*x^2])^(n+2),x] /;
FreeQ[{a,b,c,d},x] && EqQ[c^2-1] && RationalQ[n] && n<-1 && n!=-2


Int[ArcSin[a_.*x_^p_]^n_./x_,x_Symbol] :=
  1/p*Subst[Int[x^n*Cot[x],x],x,ArcSin[a*x^p]] /;
FreeQ[{a,p},x] && PositiveIntegerQ[n]


Int[ArcCos[a_.*x_^p_]^n_./x_,x_Symbol] :=
  -1/p*Subst[Int[x^n*Tan[x],x],x,ArcCos[a*x^p]] /;
FreeQ[{a,p},x] && PositiveIntegerQ[n]


Int[u_.*ArcSin[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
  Int[u*ArcCsc[a/c+b*x^n/c]^m,x] /;
FreeQ[{a,b,c,n,m},x]


Int[u_.*ArcCos[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
  Int[u*ArcSec[a/c+b*x^n/c]^m,x] /;
FreeQ[{a,b,c,n,m},x]


Int[ArcSin[Sqrt[1+b_.*x_^2]]^n_./Sqrt[1+b_.*x_^2],x_Symbol] :=
  Sqrt[-b*x^2]/(b*x)*Subst[Int[ArcSin[x]^n/Sqrt[1-x^2],x],x,Sqrt[1+b*x^2]] /;
FreeQ[{b,n},x]


Int[ArcCos[Sqrt[1+b_.*x_^2]]^n_./Sqrt[1+b_.*x_^2],x_Symbol] :=
  Sqrt[-b*x^2]/(b*x)*Subst[Int[ArcCos[x]^n/Sqrt[1-x^2],x],x,Sqrt[1+b*x^2]] /;
FreeQ[{b,n},x]


Int[u_.*f_^(c_.*ArcSin[a_.+b_.*x_]^n_.),x_Symbol] :=
  1/b*Subst[Int[ReplaceAll[u,x->-a/b+Sin[x]/b]*f^(c*x^n)*Cos[x],x],x,ArcSin[a+b*x]] /;
FreeQ[{a,b,c,f},x] && PositiveIntegerQ[n]


Int[u_.*f_^(c_.*ArcCos[a_.+b_.*x_]^n_.),x_Symbol] :=
  -1/b*Subst[Int[ReplaceAll[u,x->-a/b+Cos[x]/b]*f^(c*x^n)*Sin[x],x],x,ArcCos[a+b*x]] /;
FreeQ[{a,b,c,f},x] && PositiveIntegerQ[n]


Int[ArcSin[a_.*x_^2+b_.*Sqrt[c_+d_.*x_^2]],x_Symbol] :=
  x*ArcSin[a*x^2+b*Sqrt[c+d*x^2]] - 
  x*Sqrt[b^2*d+a^2*x^2+2*a*b*Sqrt[c+d*x^2]]/Sqrt[(-x^2)*(b^2*d+a^2*x^2+2*a*b*Sqrt[c+d*x^2])]*
    Int[x*(b*d+2*a*Sqrt[c+d*x^2])/(Sqrt[c+d*x^2]*Sqrt[b^2*d +a^2*x^2+2*a*b*Sqrt[c+d*x^2]]),x] /;
FreeQ[{a,b,c,d},x] && EqQ[b^2*c,1]


Int[ArcCos[a_.*x_^2+b_.*Sqrt[c_+d_.*x_^2]],x_Symbol] :=
  x*ArcCos[a*x^2+b*Sqrt[c+d*x^2]] + 
  x*Sqrt[b^2*d+a^2*x^2+2*a*b*Sqrt[c+d*x^2]]/Sqrt[(-x^2)*(b^2*d+a^2*x^2+2*a*b*Sqrt[c+d*x^2])]*
    Int[x*(b*d+2*a*Sqrt[c+d*x^2])/(Sqrt[c+d*x^2]*Sqrt[b^2*d+a^2*x^2+2*a*b*Sqrt[c+d*x^2]]),x] /;
FreeQ[{a,b,c,d},x] && EqQ[b^2*c,1]


Int[ArcSin[u_],x_Symbol] :=
  x*ArcSin[u] -
  Int[SimplifyIntegrand[x*D[u,x]/Sqrt[1-u^2],x],x] /;
InverseFunctionFreeQ[u,x] && Not[FunctionOfExponentialQ[u,x]]


Int[ArcCos[u_],x_Symbol] :=
  x*ArcCos[u] +
  Int[SimplifyIntegrand[x*D[u,x]/Sqrt[1-u^2],x],x] /;
InverseFunctionFreeQ[u,x] && Not[FunctionOfExponentialQ[u,x]]


Int[(c_.+d_.*x_)^m_.*(a_.+b_.*ArcSin[u_]),x_Symbol] :=
  (c+d*x)^(m+1)*(a+b*ArcSin[u])/(d*(m+1)) -
  b/(d*(m+1))*Int[SimplifyIntegrand[(c+d*x)^(m+1)*D[u,x]/Sqrt[1-u^2],x],x] /;
FreeQ[{a,b,c,d,m},x] && NeQ[m+1] && InverseFunctionFreeQ[u,x] && Not[FunctionOfQ[(c+d*x)^(m+1),u,x]] && Not[FunctionOfExponentialQ[u,x]]


Int[(c_.+d_.*x_)^m_.*(a_.+b_.*ArcCos[u_]),x_Symbol] :=
  (c+d*x)^(m+1)*(a+b*ArcCos[u])/(d*(m+1)) +
  b/(d*(m+1))*Int[SimplifyIntegrand[(c+d*x)^(m+1)*D[u,x]/Sqrt[1-u^2],x],x] /;
FreeQ[{a,b,c,d,m},x] && NeQ[m+1] && InverseFunctionFreeQ[u,x] && Not[FunctionOfQ[(c+d*x)^(m+1),u,x]] && Not[FunctionOfExponentialQ[u,x]]


Int[v_*(a_.+b_.*ArcSin[u_]),x_Symbol] :=
  With[{w=IntHide[v,x]},  
  Dist[(a+b*ArcSin[u]),w,x] -
  b*Int[SimplifyIntegrand[w*D[u,x]/Sqrt[1-u^2],x],x] /;
 InverseFunctionFreeQ[w,x]] /;
FreeQ[{a,b},x] && InverseFunctionFreeQ[u,x] && Not[MatchQ[v, (c_.+d_.*x)^m_. /; FreeQ[{c,d,m},x]]]


Int[v_*(a_.+b_.*ArcCos[u_]),x_Symbol] :=
  With[{w=IntHide[v,x]},  
  Dist[(a+b*ArcCos[u]),w,x] +
  b*Int[SimplifyIntegrand[w*D[u,x]/Sqrt[1-u^2],x],x] /;
 InverseFunctionFreeQ[w,x]] /;
FreeQ[{a,b},x] && InverseFunctionFreeQ[u,x] && Not[MatchQ[v, (c_.+d_.*x)^m_. /; FreeQ[{c,d,m},x]]]





(* ::Subsection::Closed:: *)
(*5.2.1 u (a+b arctan(c x))^n*)


Int[(a_.+b_.*ArcTan[c_.*x_])^n_.,x_Symbol] :=
  x*(a+b*ArcTan[c*x])^n -
  b*c*n*Int[x*(a+b*ArcTan[c*x])^(n-1)/(1+c^2*x^2),x] /;
FreeQ[{a,b,c},x] && PositiveIntegerQ[n]


Int[(a_.+b_.*ArcCot[c_.*x_])^n_.,x_Symbol] :=
  x*(a+b*ArcCot[c*x])^n +
  b*c*n*Int[x*(a+b*ArcCot[c*x])^(n-1)/(1+c^2*x^2),x] /;
FreeQ[{a,b,c},x] && PositiveIntegerQ[n]


Int[(a_.+b_.*ArcTan[c_.*x_])^n_,x_Symbol] :=
  Defer[Int][(a+b*ArcTan[c*x])^n,x] /;
FreeQ[{a,b,c,n},x] && Not[PositiveIntegerQ[n]]


Int[(a_.+b_.*ArcCot[c_.*x_])^n_,x_Symbol] :=
  Defer[Int][(a+b*ArcCot[c*x])^n,x] /;
FreeQ[{a,b,c,n},x] && Not[PositiveIntegerQ[n]]


Int[(a_.+b_.*ArcTan[c_.*x_])^n_./(d_+e_.*x_),x_Symbol] :=
  -(a+b*ArcTan[c*x])^n*Log[2*d/(d+e*x)]/e +
  b*c*n/e*Int[(a+b*ArcTan[c*x])^(n-1)*Log[2*d/(d+e*x)]/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d^2+e^2] && PositiveIntegerQ[n]


Int[(a_.+b_.*ArcCot[c_.*x_])^n_./(d_+e_.*x_),x_Symbol] :=
  -(a+b*ArcCot[c*x])^n*Log[2*d/(d+e*x)]/e -
  b*c*n/e*Int[(a+b*ArcCot[c*x])^(n-1)*Log[2*d/(d+e*x)]/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d^2+e^2] && PositiveIntegerQ[n]


Int[ArcTan[c_.*x_]/(d_+e_.*x_),x_Symbol] :=
  -ArcTan[c*d/e]*Log[d+e*x]/e + I*PolyLog[2,Simp[I*c*(d+e*x)/(I*c*d-e),x]]/(2*e) - I*PolyLog[2,Simp[I*c*(d+e*x)/(I*c*d+e),x]]/(2*e) /;
FreeQ[{c,d,e},x] && PositiveQ[I*c*d/e+1] && NegativeQ[I*c*d/e-1]


(* Int[ArcCot[c_.*x_]/(d_+e_.*x_),x_Symbol] :=
  ? /;
FreeQ[{c,d,e},x] && PositiveQ[I*c*d/e+1] && NegativeQ[I*c*d/e-1] *)


Int[ArcTan[c_.*x_]/(d_.+e_.*x_),x_Symbol] :=
  I/2*Int[Log[1-I*c*x]/(d+e*x),x] - I/2*Int[Log[1+I*c*x]/(d+e*x),x] /;
FreeQ[{c,d,e},x]


Int[ArcCot[c_.*x_]/(d_.+e_.*x_),x_Symbol] :=
  I/2*Int[Log[1-I/(c*x)]/(d+e*x),x] - I/2*Int[Log[1+I/(c*x)]/(d+e*x),x] /;
FreeQ[{c,d,e},x]


Int[(a_+b_.*ArcTan[c_.*x_])/(d_.+e_.*x_),x_Symbol] :=
  a/e*Log[RemoveContent[d+e*x,x]] + b*Int[ArcTan[c*x]/(d+e*x),x] /;
FreeQ[{a,b,c,d,e},x]


Int[(a_+b_.*ArcCot[c_.*x_])/(d_.+e_.*x_),x_Symbol] :=
  a/e*Log[RemoveContent[d+e*x,x]] + b*Int[ArcCot[c*x]/(d+e*x),x] /;
FreeQ[{a,b,c,d,e},x]


Int[(d_.+e_.*x_)^p_.*(a_.+b_.*ArcTan[c_.*x_]),x_Symbol] :=
  (d+e*x)^(p+1)*(a+b*ArcTan[c*x])/(e*(p+1)) - 
  b*c/(e*(p+1))*Int[(d+e*x)^(p+1)/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,p},x] && NeQ[p+1]


Int[(d_.+e_.*x_)^p_.*(a_.+b_.*ArcCot[c_.*x_]),x_Symbol] :=
  (d+e*x)^(p+1)*(a+b*ArcCot[c*x])/(e*(p+1)) + 
  b*c/(e*(p+1))*Int[(d+e*x)^(p+1)/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,p},x] && NeQ[p+1]


Int[(a_.+b_.*ArcTan[c_.*x_])^n_/x_,x_Symbol] :=
  2*(a+b*ArcTan[c*x])^n*ArcTanh[1-2*I/(I-c*x)] -
  2*b*c*n*Int[(a+b*ArcTan[c*x])^(n-1)*ArcTanh[1-2*I/(I-c*x)]/(1+c^2*x^2),x] /;
FreeQ[{a,b,c},x] && IntegerQ[n] && n>1


Int[(a_.+b_.*ArcCot[c_.*x_])^n_/x_,x_Symbol] :=
  2*(a+b*ArcCot[c*x])^n*ArcCoth[1-2*I/(I-c*x)] +
  2*b*c*n*Int[(a+b*ArcCot[c*x])^(n-1)*ArcCoth[1-2*I/(I-c*x)]/(1+c^2*x^2),x] /;
FreeQ[{a,b,c},x] && IntegerQ[n] && n>1


Int[x_^m_.*(a_.+b_.*ArcTan[c_.*x_])^n_,x_Symbol] :=
  x^(m+1)*(a+b*ArcTan[c*x])^n/(m+1) - 
  b*c*n/(m+1)*Int[x^(m+1)*(a+b*ArcTan[c*x])^(n-1)/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,m},x] && IntegerQ[n] && n>1 && NeQ[m+1]


Int[x_^m_.*(a_.+b_.*ArcCot[c_.*x_])^n_,x_Symbol] :=
  x^(m+1)*(a+b*ArcCot[c*x])^n/(m+1) + 
  b*c*n/(m+1)*Int[x^(m+1)*(a+b*ArcCot[c*x])^(n-1)/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,m},x] && IntegerQ[n] && n>1 && NeQ[m+1]


Int[(d_+e_.*x_)^p_.*(a_.+b_.*ArcTan[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^p*(a+b*ArcTan[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e},x] && PositiveIntegerQ[n,p]


Int[(d_+e_.*x_)^p_.*(a_.+b_.*ArcCot[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^p*(a+b*ArcCot[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e},x] && PositiveIntegerQ[n,p]


Int[(d_.+e_.*x_)^p_.*(a_.+b_.*ArcTan[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(d+e*x)^p*(a+b*ArcTan[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n,p},x]


Int[(d_.+e_.*x_)^p_.*(a_.+b_.*ArcCot[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(d+e*x)^p*(a+b*ArcCot[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n,p},x]


Int[x_^m_.*(a_.+b_.*ArcTan[c_.*x_])^n_./(d_+e_.*x_),x_Symbol] :=
  1/e*Int[x^(m-1)*(a+b*ArcTan[c*x])^n,x] -
  d/e*Int[x^(m-1)*(a+b*ArcTan[c*x])^n/(d+e*x),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d^2+e^2] && PositiveIntegerQ[n] && RationalQ[m] && m>0


Int[x_^m_.*(a_.+b_.*ArcCot[c_.*x_])^n_./(d_+e_.*x_),x_Symbol] :=
  1/e*Int[x^(m-1)*(a+b*ArcCot[c*x])^n,x] -
  d/e*Int[x^(m-1)*(a+b*ArcCot[c*x])^n/(d+e*x),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d^2+e^2] && PositiveIntegerQ[n] && RationalQ[m] && m>0


Int[(a_.+b_.*ArcTan[c_.*x_])^n_./(x_*(d_+e_.*x_)),x_Symbol] :=
  (a+b*ArcTan[c*x])^n*Log[2*e*x/(d+e*x)]/d - 
  b*c*n/d*Int[(a+b*ArcTan[c*x])^(n-1)*Log[2*e*x/(d+e*x)]/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d^2+e^2] && PositiveIntegerQ[n]


Int[(a_.+b_.*ArcCot[c_.*x_])^n_./(x_*(d_+e_.*x_)),x_Symbol] :=
  (a+b*ArcCot[c*x])^n*Log[2*e*x/(d+e*x)]/d +
  b*c*n/d*Int[(a+b*ArcCot[c*x])^(n-1)*Log[2*e*x/(d+e*x)]/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d^2+e^2] && PositiveIntegerQ[n]


Int[x_^m_*(a_.+b_.*ArcTan[c_.*x_])^n_./(d_+e_.*x_),x_Symbol] :=
  1/d*Int[x^m*(a+b*ArcTan[c*x])^n,x] -
  e/d*Int[x^(m+1)*(a+b*ArcTan[c*x])^n/(d+e*x),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d^2+e^2] && PositiveIntegerQ[n] && RationalQ[m] && m<-1


Int[x_^m_*(a_.+b_.*ArcCot[c_.*x_])^n_./(d_+e_.*x_),x_Symbol] :=
  1/d*Int[x^m*(a+b*ArcCot[c*x])^n,x] -
  e/d*Int[x^(m+1)*(a+b*ArcCot[c*x])^n/(d+e*x),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d^2+e^2] && PositiveIntegerQ[n] && RationalQ[m] && m<-1


Int[x_^m_.*(d_+e_.*x_)^p_.*(a_.+b_.*ArcTan[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[x^m*(d+e*x)^p*(a+b*ArcTan[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && IntegerQ[p] && PositiveIntegerQ[n] && (p>0 || NeQ[a] || IntegerQ[m])


Int[x_^m_.*(d_+e_.*x_)^p_.*(a_.+b_.*ArcCot[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[x^m*(d+e*x)^p*(a+b*ArcCot[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && IntegerQ[p] && PositiveIntegerQ[n] && (p>0 || NeQ[a] || IntegerQ[m])


Int[x_^m_.*(d_.+e_.*x_)^p_.*(a_.+b_.*ArcTan[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][x^m*(d+e*x)^p*(a+b*ArcTan[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x]


Int[x_^m_.*(d_.+e_.*x_)^p_.*(a_.+b_.*ArcCot[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][x^m*(d+e*x)^p*(a+b*ArcCot[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x]


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcTan[c_.*x_]),x_Symbol] :=
  -b*(d+e*x^2)^p/(2*c*p*(2*p+1)) + 
  x*(d+e*x^2)^p*(a+b*ArcTan[c*x])/(2*p+1) + 
  2*d*p/(2*p+1)*Int[(d+e*x^2)^(p-1)*(a+b*ArcTan[c*x]),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && RationalQ[p] && p>0


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCot[c_.*x_]),x_Symbol] :=
  b*(d+e*x^2)^p/(2*c*p*(2*p+1)) + 
  x*(d+e*x^2)^p*(a+b*ArcCot[c*x])/(2*p+1) + 
  2*d*p/(2*p+1)*Int[(d+e*x^2)^(p-1)*(a+b*ArcCot[c*x]),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && RationalQ[p] && p>0


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcTan[c_.*x_])^n_,x_Symbol] :=
  -b*n*(d+e*x^2)^p*(a+b*ArcTan[c*x])^(n-1)/(2*c*p*(2*p+1)) + 
  x*(d+e*x^2)^p*(a+b*ArcTan[c*x])^n/(2*p+1) + 
  2*d*p/(2*p+1)*Int[(d+e*x^2)^(p-1)*(a+b*ArcTan[c*x])^n,x] + 
  b^2*d*n*(n-1)/(2*p*(2*p+1))*Int[(d+e*x^2)^(p-1)*(a+b*ArcTan[c*x])^(n-2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && RationalQ[n,p] && p>0 && n>1


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCot[c_.*x_])^n_,x_Symbol] :=
  b*n*(d+e*x^2)^p*(a+b*ArcCot[c*x])^(n-1)/(2*c*p*(2*p+1)) + 
  x*(d+e*x^2)^p*(a+b*ArcCot[c*x])^n/(2*p+1) + 
  2*d*p/(2*p+1)*Int[(d+e*x^2)^(p-1)*(a+b*ArcCot[c*x])^n,x] + 
  b^2*d*n*(n-1)/(2*p*(2*p+1))*Int[(d+e*x^2)^(p-1)*(a+b*ArcCot[c*x])^(n-2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && RationalQ[n,p] && p>0 && n>1


Int[1/((d_+e_.*x_^2)*(a_.+b_.*ArcTan[c_.*x_])),x_Symbol] :=
  Log[RemoveContent[a+b*ArcTan[c*x],x]]/(b*c*d) /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d]


Int[1/((d_+e_.*x_^2)*(a_.+b_.*ArcCot[c_.*x_])),x_Symbol] :=
  -Log[RemoveContent[a+b*ArcCot[c*x],x]]/(b*c*d) /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d]


Int[(a_.+b_.*ArcTan[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  (a+b*ArcTan[c*x])^(n+1)/(b*c*d*(n+1)) /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[e-c^2*d] && NeQ[n+1]


Int[(a_.+b_.*ArcCot[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  -(a+b*ArcCot[c*x])^(n+1)/(b*c*d*(n+1)) /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[e-c^2*d] && NeQ[n+1]


Int[(a_.+b_.*ArcTan[c_.*x_])/Sqrt[d_+e_.*x_^2],x_Symbol] :=
  -2*I*(a+b*ArcTan[c*x])*ArcTan[Sqrt[1+I*c*x]/Sqrt[1-I*c*x]]/(c*Sqrt[d]) + 
  I*b*PolyLog[2,-I*Sqrt[1+I*c*x]/Sqrt[1-I*c*x]]/(c*Sqrt[d]) - 
  I*b*PolyLog[2,I*Sqrt[1+I*c*x]/Sqrt[1-I*c*x]]/(c*Sqrt[d]) /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && PositiveQ[d]


Int[(a_.+b_.*ArcCot[c_.*x_])/Sqrt[d_+e_.*x_^2],x_Symbol] :=
  -2*I*(a+b*ArcCot[c*x])*ArcTan[Sqrt[1+I*c*x]/Sqrt[1-I*c*x]]/(c*Sqrt[d]) - 
  I*b*PolyLog[2,-I*Sqrt[1+I*c*x]/Sqrt[1-I*c*x]]/(c*Sqrt[d]) + 
  I*b*PolyLog[2,I*Sqrt[1+I*c*x]/Sqrt[1-I*c*x]]/(c*Sqrt[d]) /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && PositiveQ[d]


Int[(a_.+b_.*ArcTan[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  1/(c*Sqrt[d])*Subst[Int[(a+b*x)^n*Sec[x],x],x,ArcTan[c*x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && PositiveIntegerQ[n] && PositiveQ[d]


Int[(a_.+b_.*ArcCot[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  -x*Sqrt[1+1/(c^2*x^2)]/Sqrt[d+e*x^2]*Subst[Int[(a+b*x)^n*Csc[x],x],x,ArcCot[c*x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && PositiveIntegerQ[n] && PositiveQ[d]


Int[(a_.+b_.*ArcTan[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  Sqrt[1+c^2*x^2]/Sqrt[d+e*x^2]*Int[(a+b*ArcTan[c*x])^n/Sqrt[1+c^2*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && PositiveIntegerQ[n] && Not[PositiveQ[d]]


Int[(a_.+b_.*ArcCot[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  Sqrt[1+c^2*x^2]/Sqrt[d+e*x^2]*Int[(a+b*ArcCot[c*x])^n/Sqrt[1+c^2*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && PositiveIntegerQ[n] && Not[PositiveQ[d]]


Int[(a_.+b_.*ArcTan[c_.*x_])^n_./(d_+e_.*x_^2)^2,x_Symbol] :=
  x*(a+b*ArcTan[c*x])^n/(2*d*(d+e*x^2)) + 
  (a+b*ArcTan[c*x])^(n+1)/(2*b*c*d^2*(n+1)) - 
  b*c*n/2*Int[x*(a+b*ArcTan[c*x])^(n-1)/(d+e*x^2)^2,x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && RationalQ[n] && n>0


Int[(a_.+b_.*ArcCot[c_.*x_])^n_./(d_+e_.*x_^2)^2,x_Symbol] :=
  x*(a+b*ArcCot[c*x])^n/(2*d*(d+e*x^2)) - 
  (a+b*ArcCot[c*x])^(n+1)/(2*b*c*d^2*(n+1)) + 
  b*c*n/2*Int[x*(a+b*ArcCot[c*x])^(n-1)/(d+e*x^2)^2,x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && RationalQ[n] && n>0


Int[(a_.+b_.*ArcTan[c_.*x_])/(d_+e_.*x_^2)^(3/2),x_Symbol] :=
  b/(c*d*Sqrt[d+e*x^2]) +
  x*(a+b*ArcTan[c*x])/(d*Sqrt[d+e*x^2]) /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d]


Int[(a_.+b_.*ArcCot[c_.*x_])/(d_+e_.*x_^2)^(3/2),x_Symbol] :=
  -b/(c*d*Sqrt[d+e*x^2]) +
  x*(a+b*ArcCot[c*x])/(d*Sqrt[d+e*x^2]) /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d]


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcTan[c_.*x_]),x_Symbol] :=
  b*(d+e*x^2)^(p+1)/(4*c*d*(p+1)^2) -
  x*(d+e*x^2)^(p+1)*(a+b*ArcTan[c*x])/(2*d*(p+1)) +
  (2*p+3)/(2*d*(p+1))*Int[(d+e*x^2)^(p+1)*(a+b*ArcTan[c*x]),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && RationalQ[p] && p<-1 && p!=-3/2


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCot[c_.*x_]),x_Symbol] :=
  -b*(d+e*x^2)^(p+1)/(4*c*d*(p+1)^2) -
  x*(d+e*x^2)^(p+1)*(a+b*ArcCot[c*x])/(2*d*(p+1)) +
  (2*p+3)/(2*d*(p+1))*Int[(d+e*x^2)^(p+1)*(a+b*ArcCot[c*x]),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && RationalQ[p] && p<-1 && p!=-3/2


Int[(a_.+b_.*ArcTan[c_.*x_])^n_/(d_+e_.*x_^2)^(3/2),x_Symbol] :=
  b*n*(a+b*ArcTan[c*x])^(n-1)/(c*d*Sqrt[d+e*x^2]) +
  x*(a+b*ArcTan[c*x])^n/(d*Sqrt[d+e*x^2]) -
  b^2*n*(n-1)*Int[(a+b*ArcTan[c*x])^(n-2)/(d+e*x^2)^(3/2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && RationalQ[n] && n>1


Int[(a_.+b_.*ArcCot[c_.*x_])^n_/(d_+e_.*x_^2)^(3/2),x_Symbol] :=
  -b*n*(a+b*ArcCot[c*x])^(n-1)/(c*d*Sqrt[d+e*x^2]) +
  x*(a+b*ArcCot[c*x])^n/(d*Sqrt[d+e*x^2]) -
  b^2*n*(n-1)*Int[(a+b*ArcCot[c*x])^(n-2)/(d+e*x^2)^(3/2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && RationalQ[n] && n>1


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcTan[c_.*x_])^n_,x_Symbol] :=
  b*n*(d+e*x^2)^(p+1)*(a+b*ArcTan[c*x])^(n-1)/(4*c*d*(p+1)^2) -
  x*(d+e*x^2)^(p+1)*(a+b*ArcTan[c*x])^n/(2*d*(p+1)) +
  (2*p+3)/(2*d*(p+1))*Int[(d+e*x^2)^(p+1)*(a+b*ArcTan[c*x])^n,x] -
  b^2*n*(n-1)/(4*(p+1)^2)*Int[(d+e*x^2)^p*(a+b*ArcTan[c*x])^(n-2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && RationalQ[n,p] && p<-1 && n>1 && p!=-3/2


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCot[c_.*x_])^n_,x_Symbol] :=
  -b*n*(d+e*x^2)^(p+1)*(a+b*ArcCot[c*x])^(n-1)/(4*c*d*(p+1)^2) -
  x*(d+e*x^2)^(p+1)*(a+b*ArcCot[c*x])^n/(2*d*(p+1)) +
  (2*p+3)/(2*d*(p+1))*Int[(d+e*x^2)^(p+1)*(a+b*ArcCot[c*x])^n,x] -
  b^2*n*(n-1)/(4*(p+1)^2)*Int[(d+e*x^2)^p*(a+b*ArcCot[c*x])^(n-2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && RationalQ[n,p] && p<-1 && n>1 && p!=-3/2


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcTan[c_.*x_])^n_,x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcTan[c*x])^(n+1)/(b*c*d*(n+1)) - 
  2*c*(p+1)/(b*(n+1))*Int[x*(d+e*x^2)^p*(a+b*ArcTan[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && RationalQ[n,p] && p<-1 && n<-1


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCot[c_.*x_])^n_,x_Symbol] :=
  -(d+e*x^2)^(p+1)*(a+b*ArcCot[c*x])^(n+1)/(b*c*d*(n+1)) + 
  2*c*(p+1)/(b*(n+1))*Int[x*(d+e*x^2)^p*(a+b*ArcCot[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && RationalQ[n,p] && p<-1 && n<-1


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcTan[c_.*x_])^n_.,x_Symbol] :=
  d^p/c*Subst[Int[(a+b*x)^n/Cos[x]^(2*(p+1)),x],x,ArcTan[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[e-c^2*d] && NegativeIntegerQ[2*(p+1)] && (IntegerQ[p] || PositiveQ[d])


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcTan[c_.*x_])^n_.,x_Symbol] :=
  d^(p+1/2)*Sqrt[1+c^2*x^2]/Sqrt[d+e*x^2]*Int[(1+c^2*x^2)^p*(a+b*ArcTan[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[e-c^2*d] && NegativeIntegerQ[2*(p+1)] && Not[IntegerQ[p] || PositiveQ[d]]


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCot[c_.*x_])^n_.,x_Symbol] :=
  -d^p/c*Subst[Int[(a+b*x)^n/Sin[x]^(2*(p+1)),x],x,ArcCot[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[e-c^2*d] && NegativeIntegerQ[2*(p+1)] && IntegerQ[p]


Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCot[c_.*x_])^n_.,x_Symbol] :=
  -d^(p+1/2)*x*Sqrt[(1+c^2*x^2)/(c^2*x^2)]/Sqrt[d+e*x^2]*Subst[Int[(a+b*x)^n/Sin[x]^(2*(p+1)),x],x,ArcCot[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[e-c^2*d] && NegativeIntegerQ[2*(p+1)] && Not[IntegerQ[p]]


Int[ArcTan[c_.*x_]/(d_.+e_.*x_^2),x_Symbol] :=
  I/2*Int[Log[1-I*c*x]/(d+e*x^2),x] - I/2*Int[Log[1+I*c*x]/(d+e*x^2),x] /;
FreeQ[{c,d,e},x]


Int[ArcCot[c_.*x_]/(d_.+e_.*x_^2),x_Symbol] :=
  I/2*Int[Log[1-I/(c*x)]/(d+e*x^2),x] - I/2*Int[Log[1+I/(c*x)]/(d+e*x^2),x] /;
FreeQ[{c,d,e},x]


Int[(a_+b_.*ArcTan[c_.*x_])/(d_.+e_.*x_^2),x_Symbol] :=
  a*Int[1/(d+e*x^2),x] + b*Int[ArcTan[c*x]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x]


Int[(a_+b_.*ArcCot[c_.*x_])/(d_.+e_.*x_^2),x_Symbol] :=
  a*Int[1/(d+e*x^2),x] + b*Int[ArcCot[c*x]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x]


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcTan[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(d+e*x^2)^p,x]},  
  Dist[a+b*ArcTan[c*x],u,x] - b*c*Int[ExpandIntegrand[u/(1+c^2*x^2),x],x]] /;
FreeQ[{a,b,c,d,e},x] && (IntegerQ[p] || NegativeIntegerQ[p+1/2])


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCot[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(d+e*x^2)^p,x]},  
  Dist[a+b*ArcCot[c*x],u,x] + b*c*Int[ExpandIntegrand[u/(1+c^2*x^2),x],x]] /;
FreeQ[{a,b,c,d,e},x] && (IntegerQ[p] || NegativeIntegerQ[p+1/2])


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcTan[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^2)^p*(a+b*ArcTan[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e},x] && IntegerQ[p] && PositiveIntegerQ[n]


Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCot[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^2)^p*(a+b*ArcCot[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e},x] && IntegerQ[p] && PositiveIntegerQ[n]


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcTan[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(d+e*x^2)^p*(a+b*ArcTan[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n,p},x]


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCot[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(d+e*x^2)^p*(a+b*ArcCot[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n,p},x]


Int[x_^m_*(a_.+b_.*ArcTan[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/e*Int[x^(m-2)*(a+b*ArcTan[c*x])^n,x] -
  d/e*Int[x^(m-2)*(a+b*ArcTan[c*x])^n/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && RationalQ[m,n] && n>0 && m>1


Int[x_^m_*(a_.+b_.*ArcCot[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/e*Int[x^(m-2)*(a+b*ArcCot[c*x])^n,x] -
  d/e*Int[x^(m-2)*(a+b*ArcCot[c*x])^n/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && RationalQ[m,n] && n>0 && m>1


Int[x_^m_*(a_.+b_.*ArcTan[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/d*Int[x^m*(a+b*ArcTan[c*x])^n,x] -
  e/d*Int[x^(m+2)*(a+b*ArcTan[c*x])^n/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && RationalQ[m,n] && n>0 && m<-1


Int[x_^m_*(a_.+b_.*ArcCot[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/d*Int[x^m*(a+b*ArcCot[c*x])^n,x] -
  e/d*Int[x^(m+2)*(a+b*ArcCot[c*x])^n/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && RationalQ[m,n] && n>0 && m<-1


Int[x_*(a_.+b_.*ArcTan[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  -I*(a+b*ArcTan[c*x])^(n+1)/(b*e*(n+1)) - 
  1/(c*d)*Int[(a+b*ArcTan[c*x])^n/(I-c*x),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && PositiveIntegerQ[n]


Int[x_*(a_.+b_.*ArcCot[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  I*(a+b*ArcCot[c*x])^(n+1)/(b*e*(n+1)) - 
  1/(c*d)*Int[(a+b*ArcCot[c*x])^n/(I-c*x),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && PositiveIntegerQ[n]


Int[x_*(a_.+b_.*ArcTan[c_.*x_])^n_/(d_+e_.*x_^2),x_Symbol] :=
  x*(a+b*ArcTan[c*x])^(n+1)/(b*c*d*(n+1)) - 
  1/(b*c*d*(n+1))*Int[(a+b*ArcTan[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && Not[PositiveIntegerQ[n]] && NeQ[n+1]


Int[x_*(a_.+b_.*ArcCot[c_.*x_])^n_/(d_+e_.*x_^2),x_Symbol] :=
  -x*(a+b*ArcCot[c*x])^(n+1)/(b*c*d*(n+1)) + 
  1/(b*c*d*(n+1))*Int[(a+b*ArcCot[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && Not[PositiveIntegerQ[n]] && NeQ[n+1]


Int[x_^m_*(a_.+b_.*ArcTan[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/e*Int[x^(m-2)*(a+b*ArcTan[c*x])^n,x] -
  d/e*Int[x^(m-2)*(a+b*ArcTan[c*x])^n/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && RationalQ[m,n] && n>0 && m>1


Int[x_^m_*(a_.+b_.*ArcCot[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/e*Int[x^(m-2)*(a+b*ArcCot[c*x])^n,x] -
  d/e*Int[x^(m-2)*(a+b*ArcCot[c*x])^n/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && RationalQ[m,n] && n>0 && m>1


Int[(a_.+b_.*ArcTan[c_.*x_])^n_./(x_*(d_+e_.*x_^2)),x_Symbol] :=
  -I*(a+b*ArcTan[c*x])^(n+1)/(b*d*(n+1)) +
  I/d*Int[(a+b*ArcTan[c*x])^n/(x*(I+c*x)),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && RationalQ[n] && n>0


Int[(a_.+b_.*ArcCot[c_.*x_])^n_./(x_*(d_+e_.*x_^2)),x_Symbol] :=
  I*(a+b*ArcCot[c*x])^(n+1)/(b*d*(n+1)) +
  I/d*Int[(a+b*ArcCot[c*x])^n/(x*(I+c*x)),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && RationalQ[n] && n>0


Int[x_^m_*(a_.+b_.*ArcTan[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/d*Int[x^m*(a+b*ArcTan[c*x])^n,x] -
  e/d*Int[x^(m+2)*(a+b*ArcTan[c*x])^n/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && RationalQ[m,n] && n>0 && m<-1


Int[x_^m_*(a_.+b_.*ArcCot[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/d*Int[x^m*(a+b*ArcCot[c*x])^n,x] -
  e/d*Int[x^(m+2)*(a+b*ArcCot[c*x])^n/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && RationalQ[m,n] && n>0 && m<-1


Int[x_^m_*(a_.+b_.*ArcTan[c_.*x_])^n_/(d_+e_.*x_^2),x_Symbol] :=
  x^m*(a+b*ArcTan[c*x])^(n+1)/(b*c*d*(n+1)) - 
  m/(b*c*d*(n+1))*Int[x^(m-1)*(a+b*ArcTan[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,m},x] && EqQ[e-c^2*d] && RationalQ[n] && n<-1


Int[x_^m_*(a_.+b_.*ArcCot[c_.*x_])^n_/(d_+e_.*x_^2),x_Symbol] :=
  -x^m*(a+b*ArcCot[c*x])^(n+1)/(b*c*d*(n+1)) + 
  m/(b*c*d*(n+1))*Int[x^(m-1)*(a+b*ArcCot[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,m},x] && EqQ[e-c^2*d] && RationalQ[n] && n<-1


Int[x_^m_.*(a_.+b_.*ArcTan[c_.*x_])/(d_+e_.*x_^2),x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcTan[c*x]),x^m/(d+e*x^2),x],x] /;
FreeQ[{a,b,c,d,e},x] && IntegerQ[m] && Not[m==1 && NeQ[a]]


Int[x_^m_.*(a_.+b_.*ArcCot[c_.*x_])/(d_+e_.*x_^2),x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcCot[c*x]),x^m/(d+e*x^2),x],x] /;
FreeQ[{a,b,c,d,e},x] && IntegerQ[m] && Not[m==1 && NeQ[a]]


Int[x_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcTan[c_.*x_])^n_.,x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcTan[c*x])^n/(2*e*(p+1)) - 
  b*n/(2*c*(p+1))*Int[(d+e*x^2)^p*(a+b*ArcTan[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[e-c^2*d] && RationalQ[n] && n>0 && NeQ[p+1]


Int[x_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCot[c_.*x_])^n_.,x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcCot[c*x])^n/(2*e*(p+1)) +
  b*n/(2*c*(p+1))*Int[(d+e*x^2)^p*(a+b*ArcCot[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[e-c^2*d] && RationalQ[n] && n>0 && NeQ[p+1]


Int[x_*(a_.+b_.*ArcTan[c_.*x_])^n_/(d_+e_.*x_^2)^2,x_Symbol] :=
  x*(a+b*ArcTan[c*x])^(n+1)/(b*c*d*(n+1)*(d+e*x^2)) -
  (1-c^2*x^2)*(a+b*ArcTan[c*x])^(n+2)/(b^2*e*(n+1)*(n+2)*(d+e*x^2)) -
  4/(b^2*(n+1)*(n+2))*Int[x*(a+b*ArcTan[c*x])^(n+2)/(d+e*x^2)^2,x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && RationalQ[n] && n<-1 && n!=-2


Int[x_*(a_.+b_.*ArcCot[c_.*x_])^n_/(d_+e_.*x_^2)^2,x_Symbol] :=
  -x*(a+b*ArcCot[c*x])^(n+1)/(b*c*d*(n+1)*(d+e*x^2)) -
  (1-c^2*x^2)*(a+b*ArcCot[c*x])^(n+2)/(b^2*e*(n+1)*(n+2)*(d+e*x^2)) -
  4/(b^2*(n+1)*(n+2))*Int[x*(a+b*ArcCot[c*x])^(n+2)/(d+e*x^2)^2,x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && RationalQ[n] && n<-1 && n!=-2


Int[x_^2*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcTan[c_.*x_]),x_Symbol] :=
  -b*(d+e*x^2)^(p+1)/(4*c^3*d*(p+1)^2) + 
  x*(d+e*x^2)^(p+1)*(a+b*ArcTan[c*x])/(2*c^2*d*(p+1)) - 
  1/(2*c^2*d*(p+1))*Int[(d+e*x^2)^(p+1)*(a+b*ArcTan[c*x]),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && RationalQ[p] && p<-1 && p!=-5/2


Int[x_^2*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCot[c_.*x_]),x_Symbol] :=
  b*(d+e*x^2)^(p+1)/(4*c^3*d*(p+1)^2) + 
  x*(d+e*x^2)^(p+1)*(a+b*ArcCot[c*x])/(2*c^2*d*(p+1)) - 
  1/(2*c^2*d*(p+1))*Int[(d+e*x^2)^(p+1)*(a+b*ArcCot[c*x]),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && RationalQ[p] && p<-1 && p!=-5/2


Int[x_^2*(a_.+b_.*ArcTan[c_.*x_])^n_./(d_+e_.*x_^2)^2,x_Symbol] :=
  (a+b*ArcTan[c*x])^(n+1)/(2*b*c^3*d^2*(n+1)) - 
  x*(a+b*ArcTan[c*x])^n/(2*c^2*d*(d+e*x^2)) + 
  b*n/(2*c)*Int[x*(a+b*ArcTan[c*x])^(n-1)/(d+e*x^2)^2,x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && RationalQ[n] && n>0


Int[x_^2*(a_.+b_.*ArcCot[c_.*x_])^n_./(d_+e_.*x_^2)^2,x_Symbol] :=
  -(a+b*ArcCot[c*x])^(n+1)/(2*b*c^3*d^2*(n+1)) - 
  x*(a+b*ArcCot[c*x])^n/(2*c^2*d*(d+e*x^2)) - 
  b*n/(2*c)*Int[x*(a+b*ArcCot[c*x])^(n-1)/(d+e*x^2)^2,x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && RationalQ[n] && n>0


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcTan[c_.*x_]),x_Symbol] :=
  b*x^m*(d+e*x^2)^(p+1)/(c*d*m^2) - 
  x^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcTan[c*x])/(c^2*d*m) + 
  (m-1)/(c^2*d*m)*Int[x^(m-2)*(d+e*x^2)^(p+1)*(a+b*ArcTan[c*x]),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && EqQ[m+2*p+2] && RationalQ[p] && p<-1


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCot[c_.*x_]),x_Symbol] :=
  -b*x^m*(d+e*x^2)^(p+1)/(c*d*m^2) - 
  x^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcCot[c*x])/(c^2*d*m) + 
  (m-1)/(c^2*d*m)*Int[x^(m-2)*(d+e*x^2)^(p+1)*(a+b*ArcCot[c*x]),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && EqQ[m+2*p+2] && RationalQ[p] && p<-1


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcTan[c_.*x_])^n_,x_Symbol] :=
  b*n*x^m*(d+e*x^2)^(p+1)*(a+b*ArcTan[c*x])^(n-1)/(c*d*m^2) - 
  x^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcTan[c*x])^n/(c^2*d*m) - 
  b^2*n*(n-1)/m^2*Int[x^m*(d+e*x^2)^p*(a+b*ArcTan[c*x])^(n-2),x] + 
  (m-1)/(c^2*d*m)*Int[x^(m-2)*(d+e*x^2)^(p+1)*(a+b*ArcTan[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m},x] && EqQ[e-c^2*d] && EqQ[m+2*p+2] && RationalQ[n,p] && p<-1 && n>1


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCot[c_.*x_])^n_,x_Symbol] :=
  -b*n*x^m*(d+e*x^2)^(p+1)*(a+b*ArcCot[c*x])^(n-1)/(c*d*m^2) - 
  x^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcCot[c*x])^n/(c^2*d*m) - 
  b^2*n*(n-1)/m^2*Int[x^m*(d+e*x^2)^p*(a+b*ArcCot[c*x])^(n-2),x] + 
  (m-1)/(c^2*d*m)*Int[x^(m-2)*(d+e*x^2)^(p+1)*(a+b*ArcCot[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m},x] && EqQ[e-c^2*d] && EqQ[m+2*p+2] && RationalQ[n,p] && p<-1 && n>1


Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcTan[c_.*x_])^n_,x_Symbol] :=
  x^m*(d+e*x^2)^(p+1)*(a+b*ArcTan[c*x])^(n+1)/(b*c*d*(n+1)) - 
  m/(b*c*(n+1))*Int[x^(m-1)*(d+e*x^2)^p*(a+b*ArcTan[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,m,p},x] && EqQ[e-c^2*d] && EqQ[m+2*p+2] && RationalQ[n] && n<-1


Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCot[c_.*x_])^n_,x_Symbol] :=
  -x^m*(d+e*x^2)^(p+1)*(a+b*ArcCot[c*x])^(n+1)/(b*c*d*(n+1)) + 
  m/(b*c*(n+1))*Int[x^(m-1)*(d+e*x^2)^p*(a+b*ArcCot[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,m,p},x] && EqQ[e-c^2*d] && EqQ[m+2*p+2] && RationalQ[n] && n<-1


Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcTan[c_.*x_])^n_.,x_Symbol] :=
  x^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcTan[c*x])^n/(d*(m+1)) - 
  b*c*n/(m+1)*Int[x^(m+1)*(d+e*x^2)^p*(a+b*ArcTan[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,m,p},x] && EqQ[e-c^2*d] && EqQ[m+2*p+3] && RationalQ[n] && n>0 && NeQ[m+1]


Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCot[c_.*x_])^n_.,x_Symbol] :=
  x^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcCot[c*x])^n/(d*(m+1)) + 
  b*c*n/(m+1)*Int[x^(m+1)*(d+e*x^2)^p*(a+b*ArcCot[c*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,m,p},x] && EqQ[e-c^2*d] && EqQ[m+2*p+3] && RationalQ[n] && n>0 && NeQ[m+1]


Int[x_^m_*Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcTan[c_.*x_]),x_Symbol] :=
  x^(m+1)*Sqrt[d+e*x^2]*(a+b*ArcTan[c*x])/(m+2) - 
  b*c*d/(m+2)*Int[x^(m+1)/Sqrt[d+e*x^2],x] + 
  d/(m+2)*Int[x^m*(a+b*ArcTan[c*x])/Sqrt[d+e*x^2],x] /;
FreeQ[{a,b,c,d,e,m},x] && EqQ[e-c^2*d] && NeQ[m+2]


Int[x_^m_*Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcCot[c_.*x_]),x_Symbol] :=
  x^(m+1)*Sqrt[d+e*x^2]*(a+b*ArcCot[c*x])/(m+2) + 
  b*c*d/(m+2)*Int[x^(m+1)/Sqrt[d+e*x^2],x] + 
  d/(m+2)*Int[x^m*(a+b*ArcCot[c*x])/Sqrt[d+e*x^2],x] /;
FreeQ[{a,b,c,d,e,m},x] && EqQ[e-c^2*d] && NeQ[m+2]


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcTan[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[x^m*(d+e*x^2)^p*(a+b*ArcTan[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && EqQ[e-c^2*d] && PositiveIntegerQ[n] && IntegerQ[p] && p>1


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCot[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[x^m*(d+e*x^2)^p*(a+b*ArcCot[c*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && EqQ[e-c^2*d] && PositiveIntegerQ[n] && IntegerQ[p] && p>1


Int[x_^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcTan[c_.*x_])^n_.,x_Symbol] :=
  d*Int[x^m*(d+e*x^2)^(p-1)*(a+b*ArcTan[c*x])^n,x] + 
  c^2*d*Int[x^(m+2)*(d+e*x^2)^(p-1)*(a+b*ArcTan[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m},x] && EqQ[e-c^2*d] && RationalQ[p] && p>0 && PositiveIntegerQ[n] && (RationalQ[m] || EqQ[n,1] && IntegerQ[p])


Int[x_^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCot[c_.*x_])^n_.,x_Symbol] :=
  d*Int[x^m*(d+e*x^2)^(p-1)*(a+b*ArcCot[c*x])^n,x] + 
  c^2*d*Int[x^(m+2)*(d+e*x^2)^(p-1)*(a+b*ArcCot[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m},x] && EqQ[e-c^2*d] && RationalQ[p] && p>0 && PositiveIntegerQ[n] && (RationalQ[m] || EqQ[n,1] && IntegerQ[p])


Int[x_^m_*(a_.+b_.*ArcTan[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  x^(m-1)*Sqrt[d+e*x^2]*(a+b*ArcTan[c*x])^n/(c^2*d*m) - 
  b*n/(c*m)*Int[x^(m-1)*(a+b*ArcTan[c*x])^(n-1)/Sqrt[d+e*x^2],x] - 
  (m-1)/(c^2*m)*Int[x^(m-2)*(a+b*ArcTan[c*x])^n/Sqrt[d+e*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && RationalQ[m,n] && n>0 && m>1


Int[x_^m_*(a_.+b_.*ArcCot[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  x^(m-1)*Sqrt[d+e*x^2]*(a+b*ArcCot[c*x])^n/(c^2*d*m) + 
  b*n/(c*m)*Int[x^(m-1)*(a+b*ArcCot[c*x])^(n-1)/Sqrt[d+e*x^2],x] - 
  (m-1)/(c^2*m)*Int[x^(m-2)*(a+b*ArcCot[c*x])^n/Sqrt[d+e*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && RationalQ[m,n] && n>0 && m>1


Int[(a_.+b_.*ArcTan[c_.*x_])/(x_*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  -2/Sqrt[d]*(a+b*ArcTan[c*x])*ArcTanh[Sqrt[1+I*c*x]/Sqrt[1-I*c*x]] + 
  I*b/Sqrt[d]*PolyLog[2,-Sqrt[1+I*c*x]/Sqrt[1-I*c*x]] - 
  I*b/Sqrt[d]*PolyLog[2,Sqrt[1+I*c*x]/Sqrt[1-I*c*x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && PositiveQ[d]


Int[(a_.+b_.*ArcCot[c_.*x_])/(x_*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  -2/Sqrt[d]*(a+b*ArcCot[c*x])*ArcTanh[Sqrt[1+I*c*x]/Sqrt[1-I*c*x]] - 
  I*b/Sqrt[d]*PolyLog[2,-Sqrt[1+I*c*x]/Sqrt[1-I*c*x]] + 
  I*b/Sqrt[d]*PolyLog[2,Sqrt[1+I*c*x]/Sqrt[1-I*c*x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && PositiveQ[d]


Int[(a_.+b_.*ArcTan[c_.*x_])^n_/(x_*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  1/Sqrt[d]*Subst[Int[(a+b*x)^n*Csc[x],x],x,ArcTan[c*x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && PositiveIntegerQ[n] && PositiveQ[d]


Int[(a_.+b_.*ArcCot[c_.*x_])^n_/(x_*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  -c*x*Sqrt[1+1/(c^2*x^2)]/Sqrt[d+e*x^2]*Subst[Int[(a+b*x)^n*Sec[x],x],x,ArcCot[c*x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && PositiveIntegerQ[n] && PositiveQ[d]


Int[(a_.+b_.*ArcTan[c_.*x_])^n_./(x_*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  Sqrt[1+c^2*x^2]/Sqrt[d+e*x^2]*Int[(a+b*ArcTan[c*x])^n/(x*Sqrt[1+c^2*x^2]),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && PositiveIntegerQ[n] && Not[PositiveQ[d]]


Int[(a_.+b_.*ArcCot[c_.*x_])^n_./(x_*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  Sqrt[1+c^2*x^2]/Sqrt[d+e*x^2]*Int[(a+b*ArcCot[c*x])^n/(x*Sqrt[1+c^2*x^2]),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && PositiveIntegerQ[n] && Not[PositiveQ[d]]


Int[(a_.+b_.*ArcTan[c_.*x_])^n_./(x_^2*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  -Sqrt[d+e*x^2]*(a+b*ArcTan[c*x])^n/(d*x) + 
  b*c*n*Int[(a+b*ArcTan[c*x])^(n-1)/(x*Sqrt[d+e*x^2]),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && RationalQ[n] && n>0


Int[(a_.+b_.*ArcCot[c_.*x_])^n_./(x_^2*Sqrt[d_+e_.*x_^2]),x_Symbol] :=
  -Sqrt[d+e*x^2]*(a+b*ArcCot[c*x])^n/(d*x) - 
  b*c*n*Int[(a+b*ArcCot[c*x])^(n-1)/(x*Sqrt[d+e*x^2]),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && RationalQ[n] && n>0


Int[x_^m_*(a_.+b_.*ArcTan[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  x^(m+1)*Sqrt[d+e*x^2]*(a+b*ArcTan[c*x])^n/(d*(m+1)) - 
  b*c*n/(m+1)*Int[x^(m+1)*(a+b*ArcTan[c*x])^(n-1)/Sqrt[d+e*x^2],x] - 
  c^2*(m+2)/(m+1)*Int[x^(m+2)*(a+b*ArcTan[c*x])^n/Sqrt[d+e*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && RationalQ[m,n] && n>0 && m<-1 && m!=-2


Int[x_^m_*(a_.+b_.*ArcCot[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
  x^(m+1)*Sqrt[d+e*x^2]*(a+b*ArcCot[c*x])^n/(d*(m+1)) + 
  b*c*n/(m+1)*Int[x^(m+1)*(a+b*ArcCot[c*x])^(n-1)/Sqrt[d+e*x^2],x] - 
  c^2*(m+2)/(m+1)*Int[x^(m+2)*(a+b*ArcCot[c*x])^n/Sqrt[d+e*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && RationalQ[m,n] && n>0 && m<-1 && m!=-2


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcTan[c_.*x_])^n_.,x_Symbol] :=
  1/e*Int[x^(m-2)*(d+e*x^2)^(p+1)*(a+b*ArcTan[c*x])^n,x] -
  d/e*Int[x^(m-2)*(d+e*x^2)^p*(a+b*ArcTan[c*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && IntegersQ[m,n,2*p] && p<-1 && m>1 && n!=-1


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCot[c_.*x_])^n_.,x_Symbol] :=
  1/e*Int[x^(m-2)*(d+e*x^2)^(p+1)*(a+b*ArcCot[c*x])^n,x] -
  d/e*Int[x^(m-2)*(d+e*x^2)^p*(a+b*ArcCot[c*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && IntegersQ[m,n,2*p] && p<-1 && m>1 && n!=-1


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcTan[c_.*x_])^n_.,x_Symbol] :=
  1/d*Int[x^m*(d+e*x^2)^(p+1)*(a+b*ArcTan[c*x])^n,x] -
  e/d*Int[x^(m+2)*(d+e*x^2)^p*(a+b*ArcTan[c*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && IntegersQ[m,n,2*p] && p<-1 && m<0 && n!=-1


Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCot[c_.*x_])^n_.,x_Symbol] :=
  1/d*Int[x^m*(d+e*x^2)^(p+1)*(a+b*ArcCot[c*x])^n,x] -
  e/d*Int[x^(m+2)*(d+e*x^2)^p*(a+b*ArcCot[c*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && IntegersQ[m,n,2*p] && p<-1 && m<0 && n!=-1


Int[x_^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcTan[c_.*x_])^n_.,x_Symbol] :=
  x^m*(d+e*x^2)^(p+1)*(a+b*ArcTan[c*x])^(n+1)/(b*c*d*(n+1)) - 
  m/(b*c*(n+1))*Int[x^(m-1)*(d+e*x^2)^p*(a+b*ArcTan[c*x])^(n+1),x] - 
  c*(m+2*p+2)/(b*(n+1))*Int[x^(m+1)*(d+e*x^2)^p*(a+b*ArcTan[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && RationalQ[m,n,p] && p<-1 && n<-1 && NeQ[m+2*p+2]


Int[x_^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCot[c_.*x_])^n_.,x_Symbol] :=
  -x^m*(d+e*x^2)^(p+1)*(a+b*ArcCot[c*x])^(n+1)/(b*c*d*(n+1)) + 
  m/(b*c*(n+1))*Int[x^(m-1)*(d+e*x^2)^p*(a+b*ArcCot[c*x])^(n+1),x] + 
  c*(m+2*p+2)/(b*(n+1))*Int[x^(m+1)*(d+e*x^2)^p*(a+b*ArcCot[c*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && RationalQ[m,n,p] && p<-1 && n<-1 && NeQ[m+2*p+2]


Int[x_^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcTan[c_.*x_])^n_.,x_Symbol] :=
  d^p/c^(m+1)*Subst[Int[(a+b*x)^n*Sin[x]^m/Cos[x]^(m+2*(p+1)),x],x,ArcTan[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[e-c^2*d] && PositiveIntegerQ[m] && NegativeIntegerQ[m+2*p+1] && (IntegerQ[p] || PositiveQ[d])


Int[x_^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcTan[c_.*x_])^n_.,x_Symbol] :=
  d^(p+1/2)*Sqrt[1+c^2*x^2]/Sqrt[d+e*x^2]*Int[x^m*(1+c^2*x^2)^p*(a+b*ArcTan[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[e-c^2*d] && PositiveIntegerQ[m] && NegativeIntegerQ[m+2*p+1] && Not[IntegerQ[p] || PositiveQ[d]]


Int[x_^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCot[c_.*x_])^n_.,x_Symbol] :=
  -d^p/c^(m+1)*Subst[Int[(a+b*x)^n*Cos[x]^m/Sin[x]^(m+2*(p+1)),x],x,ArcCot[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[e-c^2*d] && PositiveIntegerQ[m] && NegativeIntegerQ[m+2*p+1] && IntegerQ[p]


Int[x_^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCot[c_.*x_])^n_.,x_Symbol] :=
  -d^(p+1/2)*x*Sqrt[(1+c^2*x^2)/(c^2*x^2)]/(c^m*Sqrt[d+e*x^2])*Subst[Int[(a+b*x)^n*Cos[x]^m/Sin[x]^(m+2*(p+1)),x],x,ArcCot[c*x]] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[e-c^2*d] && PositiveIntegerQ[m] && NegativeIntegerQ[m+2*p+1] && Not[IntegerQ[p]]


Int[x_*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcTan[c_.*x_]),x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcTan[c*x])/(2*e*(p+1)) - 
  b*c/(2*e*(p+1))*Int[(d+e*x^2)^(p+1)/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,p},x] && NeQ[p+1]


Int[x_*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCot[c_.*x_]),x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcCot[c*x])/(2*e*(p+1)) + 
  b*c/(2*e*(p+1))*Int[(d+e*x^2)^(p+1)/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,p},x] && NeQ[p+1]


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcTan[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[x^m*(d+e*x^2)^p,x]},  
  Dist[a+b*ArcTan[c*x],u,x] - b*c*Int[SimplifyIntegrand[u/(1+c^2*x^2),x],x]] /;
FreeQ[{a,b,c,d,e,m,p},x] && (
  PositiveIntegerQ[p] && Not[NegativeIntegerQ[(m-1)/2] && m+2*p+3>0] || 
  PositiveIntegerQ[(m+1)/2] && Not[NegativeIntegerQ[p] && m+2*p+3>0] || 
  NegativeIntegerQ[(m+2*p+1)/2] && Not[NegativeIntegerQ[(m-1)/2]] )


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCot[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[x^m*(d+e*x^2)^p,x]},  
  Dist[a+b*ArcCot[c*x],u,x] + b*c*Int[SimplifyIntegrand[u/(1+c^2*x^2),x],x]] /;
FreeQ[{a,b,c,d,e,m,p},x] && (
  PositiveIntegerQ[p] && Not[NegativeIntegerQ[(m-1)/2] && m+2*p+3>0] || 
  PositiveIntegerQ[(m+1)/2] && Not[NegativeIntegerQ[p] && m+2*p+3>0] || 
  NegativeIntegerQ[(m+2*p+1)/2] && Not[NegativeIntegerQ[(m-1)/2]] )


Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcTan[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcTan[c*x])^n,x^m*(d+e*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && IntegerQ[p] && PositiveIntegerQ[n] && (p>0 || p<-1 && IntegerQ[m] && m!=1)


Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCot[c_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*ArcCot[c*x])^n,x^m*(d+e*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && IntegerQ[p] && PositiveIntegerQ[n] && (p>0 || p<-1 && IntegerQ[m] && m!=1)


Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_+b_.*ArcTan[c_.*x_]),x_Symbol] :=
  a*Int[x^m*(d+e*x^2)^p,x] + b*Int[x^m*(d+e*x^2)^p*ArcTan[c*x],x] /;
FreeQ[{a,b,c,d,e,m,p},x]


Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_+b_.*ArcCot[c_.*x_]),x_Symbol] :=
  a*Int[x^m*(d+e*x^2)^p,x] + b*Int[x^m*(d+e*x^2)^p*ArcCot[c*x],x] /;
FreeQ[{a,b,c,d,e,m,p},x]


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcTan[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][x^m*(d+e*x^2)^p*(a+b*ArcTan[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x]


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCot[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][x^m*(d+e*x^2)^p*(a+b*ArcCot[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x]


Int[ArcTanh[u_]*(a_.+b_.*ArcTan[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/2*Int[Log[1+u]*(a+b*ArcTan[c*x])^n/(d+e*x^2),x] -
  1/2*Int[Log[1-u]*(a+b*ArcTan[c*x])^n/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && RationalQ[n] && n>0 && EqQ[u^2-(1-2*I/(I+c*x))^2]


Int[ArcCoth[u_]*(a_.+b_.*ArcCot[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/2*Int[Log[SimplifyIntegrand[1+1/u,x]]*(a+b*ArcCot[c*x])^n/(d+e*x^2),x] -
  1/2*Int[Log[SimplifyIntegrand[1-1/u,x]]*(a+b*ArcCot[c*x])^n/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && RationalQ[n] && n>0 && EqQ[u^2-(1-2*I/(I+c*x))^2]


Int[ArcTanh[u_]*(a_.+b_.*ArcTan[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/2*Int[Log[1+u]*(a+b*ArcTan[c*x])^n/(d+e*x^2),x] -
  1/2*Int[Log[1-u]*(a+b*ArcTan[c*x])^n/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && RationalQ[n] && n>0 && EqQ[u^2-(1-2*I/(I-c*x))^2]


Int[ArcCoth[u_]*(a_.+b_.*ArcCot[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  1/2*Int[Log[SimplifyIntegrand[1+1/u,x]]*(a+b*ArcCot[c*x])^n/(d+e*x^2),x] -
  1/2*Int[Log[SimplifyIntegrand[1-1/u,x]]*(a+b*ArcCot[c*x])^n/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && RationalQ[n] && n>0 && EqQ[u^2-(1-2*I/(I-c*x))^2]


Int[(a_.+b_.*ArcTan[c_.*x_])^n_.*Log[u_]/(d_+e_.*x_^2),x_Symbol] :=
  I*(a+b*ArcTan[c*x])^n*PolyLog[2,Together[1-u]]/(2*c*d) -
  b*n*I/2*Int[(a+b*ArcTan[c*x])^(n-1)*PolyLog[2,Together[1-u]]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && RationalQ[n] && n>0 && EqQ[(1-u)^2-(1-2*I/(I+c*x))^2]


Int[(a_.+b_.*ArcCot[c_.*x_])^n_.*Log[u_]/(d_+e_.*x_^2),x_Symbol] :=
  I*(a+b*ArcCot[c*x])^n*PolyLog[2,Together[1-u]]/(2*c*d) +
  b*n*I/2*Int[(a+b*ArcCot[c*x])^(n-1)*PolyLog[2,Together[1-u]]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && RationalQ[n] && n>0 && EqQ[(1-u)^2-(1-2*I/(I+c*x))^2]


Int[(a_.+b_.*ArcTan[c_.*x_])^n_.*Log[u_]/(d_+e_.*x_^2),x_Symbol] :=
  -I*(a+b*ArcTan[c*x])^n*PolyLog[2,Together[1-u]]/(2*c*d) +
  b*n*I/2*Int[(a+b*ArcTan[c*x])^(n-1)*PolyLog[2,Together[1-u]]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && RationalQ[n] && n>0 && EqQ[(1-u)^2-(1-2*I/(I-c*x))^2]


Int[(a_.+b_.*ArcCot[c_.*x_])^n_.*Log[u_]/(d_+e_.*x_^2),x_Symbol] :=
  -I*(a+b*ArcCot[c*x])^n*PolyLog[2,Together[1-u]]/(2*c*d) -
  b*n*I/2*Int[(a+b*ArcCot[c*x])^(n-1)*PolyLog[2,Together[1-u]]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && RationalQ[n] && n>0 && EqQ[(1-u)^2-(1-2*I/(I-c*x))^2]


Int[(a_.+b_.*ArcTan[c_.*x_])^n_.*PolyLog[p_,u_]/(d_+e_.*x_^2),x_Symbol] :=
  -I*(a+b*ArcTan[c*x])^n*PolyLog[p+1,u]/(2*c*d) +
  b*n*I/2*Int[(a+b*ArcTan[c*x])^(n-1)*PolyLog[p+1,u]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[e-c^2*d] && RationalQ[n] && n>0 && EqQ[u^2-(1-2*I/(I+c*x))^2]


Int[(a_.+b_.*ArcCot[c_.*x_])^n_.*PolyLog[p_,u_]/(d_+e_.*x_^2),x_Symbol] :=
  -I*(a+b*ArcCot[c*x])^n*PolyLog[p+1,u]/(2*c*d) -
  b*n*I/2*Int[(a+b*ArcCot[c*x])^(n-1)*PolyLog[p+1,u]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[e-c^2*d] && RationalQ[n] && n>0 && EqQ[u^2-(1-2*I/(I+c*x))^2]


Int[(a_.+b_.*ArcTan[c_.*x_])^n_.*PolyLog[p_,u_]/(d_+e_.*x_^2),x_Symbol] :=
  I*(a+b*ArcTan[c*x])^n*PolyLog[p+1,u]/(2*c*d) -
  b*n*I/2*Int[(a+b*ArcTan[c*x])^(n-1)*PolyLog[p+1,u]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[e-c^2*d] && RationalQ[n] && n>0 && EqQ[u^2-(1-2*I/(I-c*x))^2]


Int[(a_.+b_.*ArcCot[c_.*x_])^n_.*PolyLog[p_,u_]/(d_+e_.*x_^2),x_Symbol] :=
  I*(a+b*ArcCot[c*x])^n*PolyLog[p+1,u]/(2*c*d) +
  b*n*I/2*Int[(a+b*ArcCot[c*x])^(n-1)*PolyLog[p+1,u]/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[e-c^2*d] && RationalQ[n] && n>0 && EqQ[u^2-(1-2*I/(I-c*x))^2]


Int[1/((d_+e_.*x_^2)*(a_.+b_.*ArcCot[c_.*x_])*(a_.+b_.*ArcTan[c_.*x_])),x_Symbol] :=
  (-Log[a+b*ArcCot[c*x]]+Log[a+b*ArcTan[c*x]])/(b*c*d*(2*a+b*ArcCot[c*x]+b*ArcTan[c*x])) /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d]


Int[(a_.+b_.*ArcCot[c_.*x_])^m_.*(a_.+b_.*ArcTan[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  -(a+b*ArcCot[c*x])^(m+1)*(a+b*ArcTan[c*x])^n/(b*c*d*(m+1)) +
  n/(m+1)*Int[(a+b*ArcCot[c*x])^(m+1)*(a+b*ArcTan[c*x])^(n-1)/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && IntegersQ[m,n] && 0<n<=m


Int[(a_.+b_.*ArcTan[c_.*x_])^m_.*(a_.+b_.*ArcCot[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
  (a+b*ArcTan[c*x])^(m+1)*(a+b*ArcCot[c*x])^n/(b*c*d*(m+1)) +
  n/(m+1)*Int[(a+b*ArcTan[c*x])^(m+1)*(a+b*ArcCot[c*x])^(n-1)/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[e-c^2*d] && IntegersQ[m,n] && 0<n<m


Int[ArcTan[a_.*x_]/(c_+d_.*x_^n_.),x_Symbol] :=
  I/2*Int[Log[1-I*a*x]/(c+d*x^n),x] -
  I/2*Int[Log[1+I*a*x]/(c+d*x^n),x] /;
FreeQ[{a,c,d},x] && IntegerQ[n] && Not[n==2 && EqQ[d-a^2*c]]


Int[ArcCot[a_.*x_]/(c_+d_.*x_^n_.),x_Symbol] :=
  I/2*Int[Log[1-I/(a*x)]/(c+d*x^n),x] -
  I/2*Int[Log[1+I/(a*x)]/(c+d*x^n),x] /;
FreeQ[{a,c,d},x] && IntegerQ[n] && Not[n==2 && EqQ[d-a^2*c]]


Int[(d_.+e_.*Log[f_.+g_.*x_^2])*(a_.+b_.*ArcTan[c_.*x_]),x_Symbol] :=
  x*(d+e*Log[f+g*x^2])*(a+b*ArcTan[c*x]) - 
  2*e*g*Int[x^2*(a+b*ArcTan[c*x])/(f+g*x^2),x] - 
  b*c*Int[x*(d+e*Log[f+g*x^2])/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g},x]


Int[(d_.+e_.*Log[f_.+g_.*x_^2])*(a_.+b_.*ArcCot[c_.*x_]),x_Symbol] :=
  x*(d+e*Log[f+g*x^2])*(a+b*ArcCot[c*x]) - 
  2*e*g*Int[x^2*(a+b*ArcCot[c*x])/(f+g*x^2),x] + 
  b*c*Int[x*(d+e*Log[f+g*x^2])/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g},x]


Int[x_^m_.*(d_.+e_.*Log[f_.+g_.*x_^2])*(a_.+b_.*ArcTan[c_.*x_]),x_Symbol] :=
  x^(m+1)*(d+e*Log[f+g*x^2])*(a+b*ArcTan[c*x])/(m+1) - 
  2*e*g/(m+1)*Int[x^(m+2)*(a+b*ArcTan[c*x])/(f+g*x^2),x] - 
  b*c/(m+1)*Int[x^(m+1)*(d+e*Log[f+g*x^2])/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NegativeIntegerQ[m/2]


Int[x_^m_.*(d_.+e_.*Log[f_.+g_.*x_^2])*(a_.+b_.*ArcCot[c_.*x_]),x_Symbol] :=
  x^(m+1)*(d+e*Log[f+g*x^2])*(a+b*ArcCot[c*x])/(m+1) - 
  2*e*g/(m+1)*Int[x^(m+2)*(a+b*ArcCot[c*x])/(f+g*x^2),x] + 
  b*c/(m+1)*Int[x^(m+1)*(d+e*Log[f+g*x^2])/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NegativeIntegerQ[m/2]


Int[x_^m_.*(d_.+e_.*Log[f_.+g_.*x_^2])*(a_.+b_.*ArcTan[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[x^m*(d+e*Log[f+g*x^2]),x]},  
  Dist[a+b*ArcTan[c*x],u,x] - b*c*Int[ExpandIntegrand[u/(1+c^2*x^2),x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && PositiveIntegerQ[(m+1)/2]


Int[x_^m_.*(d_.+e_.*Log[f_.+g_.*x_^2])*(a_.+b_.*ArcCot[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[x^m*(d+e*Log[f+g*x^2]),x]},  
  Dist[a+b*ArcCot[c*x],u,x] + b*c*Int[ExpandIntegrand[u/(1+c^2*x^2),x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && PositiveIntegerQ[(m+1)/2]


Int[x_^m_.*(d_.+e_.*Log[f_.+g_.*x_^2])*(a_.+b_.*ArcTan[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[x^m*(a+b*ArcTan[c*x]),x]},  
  Dist[d+e*Log[f+g*x^2],u,x] - 2*e*g*Int[ExpandIntegrand[x*u/(f+g*x^2),x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && IntegerQ[m] && m!=-1


Int[x_^m_.*(d_.+e_.*Log[f_.+g_.*x_^2])*(a_.+b_.*ArcCot[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[x^m*(a+b*ArcCot[c*x]),x]},  
  Dist[d+e*Log[f+g*x^2],u,x] - 2*e*g*Int[ExpandIntegrand[x*u/(f+g*x^2),x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && IntegerQ[m] && m!=-1


Int[x_*(d_.+e_.*Log[f_+g_.*x_^2])*(a_.+b_.*ArcTan[c_.*x_])^2,x_Symbol] :=
  (f+g*x^2)*(d+e*Log[f+g*x^2])*(a+b*ArcTan[c*x])^2/(2*g) - 
  e*x^2*(a+b*ArcTan[c*x])^2/2 - 
  b/c*Int[(d+e*Log[f+g*x^2])*(a+b*ArcTan[c*x]),x] + 
  b*c*e*Int[x^2*(a+b*ArcTan[c*x])/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[g-c^2*f]


Int[x_*(d_.+e_.*Log[f_+g_.*x_^2])*(a_.+b_.*ArcCot[c_.*x_])^2,x_Symbol] :=
  (f+g*x^2)*(d+e*Log[f+g*x^2])*(a+b*ArcCot[c*x])^2/(2*g) - 
  e*x^2*(a+b*ArcCot[c*x])^2/2 + 
  b/c*Int[(d+e*Log[f+g*x^2])*(a+b*ArcCot[c*x]),x] - 
  b*c*e*Int[x^2*(a+b*ArcCot[c*x])/(1+c^2*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[g-c^2*f]





(* ::Subsection::Closed:: *)
(*5.2.2 Exponentials of inverse tangent*)


Int[E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
  Int[((1-I*a*x)^((I*n+1)/2)/((1+I*a*x)^((I*n-1)/2)*Sqrt[1+a^2*x^2])),x] /;
FreeQ[a,x] && OddQ[I*n]


Int[x_^m_.*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
  Int[x^m*((1-I*a*x)^((I*n+1)/2)/((1+I*a*x)^((I*n-1)/2)*Sqrt[1+a^2*x^2])),x] /;
FreeQ[{a,m},x] && OddQ[I*n]


Int[E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  Int[(1-I*a*x)^(I*n/2)/(1+I*a*x)^(I*n/2),x] /;
FreeQ[{a,n},x] && Not[OddQ[I*n]]


Int[x_^m_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  Int[x^m*(1-I*a*x)^(I*n/2)/(1+I*a*x)^(I*n/2),x] /;
FreeQ[{a,m,n},x] && Not[OddQ[I*n]]


Int[u_.*(c_+d_.*x_)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  c^p*Int[u*(1+d*x/c)^p*(1-I*a*x)^(I*n/2)/(1+I*a*x)^(I*n/2),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[a^2*c^2+d^2] && (IntegerQ[p] || PositiveQ[c])


Int[u_.*(c_+d_.*x_)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  Int[u*(c+d*x)^p*(1-I*a*x)^(I*n/2)/(1+I*a*x)^(I*n/2),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[a^2*c^2+d^2] && Not[IntegerQ[p] || PositiveQ[c]]


Int[u_.*(c_+d_./x_)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  d^p*Int[u/x^p*(1+c*x/d)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n},x] && EqQ[c^2+a^2*d^2] && IntegerQ[p]


Int[u_.*(c_+d_./x_)^p_*E^(n_*ArcTanh[a_.*x_]),x_Symbol] :=
  (-1)^(n/2)*c^p*Int[u*(1+d/(c*x))^p*(1-1/(I*a*x))^(I*n/2)/(1+1/(I*a*x))^(I*n/2),x] /;
FreeQ[{a,c,d,p},x] && EqQ[c^2+a^2*d^2] && Not[IntegerQ[p]] && IntegerQ[I*n/2] && PositiveQ[c]


Int[u_.*(c_+d_./x_)^p_*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
  Int[u*(c+d/x)^p*(1-I*a*x)^(I*n/2)/(1+I*a*x)^(I*n/2),x] /;
FreeQ[{a,c,d,p},x] && EqQ[c^2+a^2*d^2] && Not[IntegerQ[p]] && IntegerQ[I*n/2] && Not[PositiveQ[c]]


Int[u_.*(c_+d_./x_)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  x^p*(c+d/x)^p/(1+c*x/d)^p*Int[u/x^p*(1+c*x/d)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[c^2+a^2*d^2] && Not[IntegerQ[p]]


Int[E^(n_.*ArcTan[a_.*x_])/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  (n+a*x)*E^(n*ArcTan[a*x])/(a*c*(n^2+1)*Sqrt[c+d*x^2]) /;
FreeQ[{a,c,d,n},x] && EqQ[d-a^2*c] && Not[IntegerQ[I*n]]


Int[(c_+d_.*x_^2)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  (n-2*a*(p+1)*x)*(c+d*x^2)^(p+1)*E^(n*ArcTan[a*x])/(a*c*(n^2+4*(p+1)^2)) + 
  2*(p+1)*(2*p+3)/(c*(n^2+4*(p+1)^2))*Int[(c+d*x^2)^(p+1)*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n},x] && EqQ[d-a^2*c] && RationalQ[p] && p<-1 && Not[IntegerQ[I*n]] && NeQ[n^2+4*(p+1)^2] && IntegerQ[2*p]


Int[E^(n_.*ArcTan[a_.*x_])/(c_+d_.*x_^2),x_Symbol] :=
  E^(n*ArcTan[a*x])/(a*c*n) /;
FreeQ[{a,c,d,n},x] && EqQ[d-a^2*c]


Int[(c_+d_.*x_^2)^p_.*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
  c^p*Int[(1+a^2*x^2)^(p-I*n/2)*(1-I*a*x)^(I*n),x] /;
FreeQ[{a,c,d,p},x] && EqQ[d-a^2*c] && IntegerQ[p] && IntegerQ[(I*n+1)/2] && Not[IntegerQ[p-I*n/2]]


Int[(c_+d_.*x_^2)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  c^p*Int[(1-I*a*x)^(p+I*n/2)*(1+I*a*x)^(p-I*n/2),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[d-a^2*c] && (IntegerQ[p] || PositiveQ[c])


Int[(c_+d_.*x_^2)^p_*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
  c^(I*n/2)*Int[(c+d*x^2)^(p-I*n/2)*(1-I*a*x)^(I*n),x] /;
FreeQ[{a,c,d,p},x] && EqQ[d-a^2*c] && Not[IntegerQ[p] || PositiveQ[c]] && PositiveIntegerQ[I*n/2]


Int[(c_+d_.*x_^2)^p_*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
  1/c^(I*n/2)*Int[(c+d*x^2)^(p+I*n/2)/(1+I*a*x)^(I*n),x] /;
FreeQ[{a,c,d,p},x] && EqQ[d-a^2*c] && Not[IntegerQ[p] || PositiveQ[c]] && NegativeIntegerQ[I*n/2]


Int[(c_+d_.*x_^2)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  c^IntPart[p]*(c+d*x^2)^FracPart[p]/(1+a^2*x^2)^FracPart[p]*Int[(1+a^2*x^2)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[d-a^2*c] && Not[IntegerQ[p] || PositiveQ[c]]


Int[x_*E^(n_.*ArcTan[a_.*x_])/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  -(1-a*n*x)*E^(n*ArcTan[a*x])/(d*(n^2+1)*Sqrt[c+d*x^2]) /;
FreeQ[{a,c,d,n},x] && EqQ[d-a^2*c] && Not[IntegerQ[I*n]]


Int[x_*(c_+d_.*x_^2)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  (c+d*x^2)^(p+1)*E^(n*ArcTan[a*x])/(2*d*(p+1)) - a*c*n/(2*d*(p+1))*Int[(c+d*x^2)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n},x] && EqQ[d-a^2*c] && RationalQ[p] && p<-1 && Not[IntegerQ[I*n]] && IntegerQ[2*p]


(* Int[x_*(c_+d_.*x_^2)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  (2*(p+1)+a*n*x)*(c+d*x^2)^(p+1)*E^(n*ArcTan[a*x])/(a^2*c*(n^2+4*(p+1)^2)) - 
  n*(2*p+3)/(a*c*(n^2+4*(p+1)^2))*Int[(c+d*x^2)^(p+1)*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n},x] && EqQ[d-a^2*c] && RationalQ[p] && p<-1 && NeQ[n^2+4*(p+1)^2] && Not[IntegerQ[I*n]] *)


Int[x_^2*(c_+d_.*x_^2)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  -(1-a*n*x)*(c+d*x^2)^(p+1)*E^(n*ArcTan[a*x])/(a*d*n*(n^2+1)) /;
FreeQ[{a,c,d,n},x] && EqQ[d-a^2*c] && EqQ[n^2-2*(p+1)] && Not[IntegerQ[I*n]]


Int[x_^2*(c_+d_.*x_^2)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  -(n-2*(p+1)*a*x)*(c+d*x^2)^(p+1)*E^(n*ArcTan[a*x])/(a*d*(n^2+4*(p+1)^2)) + 
  (n^2-2*(p+1))/(d*(n^2+4*(p+1)^2))*Int[(c+d*x^2)^(p+1)*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n},x] && EqQ[d-a^2*c] && RationalQ[p] && p<-1 && Not[IntegerQ[I*n]] && NeQ[n^2+4*(p+1)^2] && 
  IntegerQ[2*p]


Int[x_^m_.*(c_+d_.*x_^2)^p_.*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
  c^p*Int[x^m*(1+a^2*x^2)^(p-I*n/2)*(1-I*a*x)^(I*n),x] /;
FreeQ[{a,c,d,m,p},x] && EqQ[d-a^2*c] && (IntegerQ[p] || PositiveQ[c]) && IntegerQ[(I*n+1)/2] && Not[IntegerQ[p-I*n/2]]


Int[x_^m_.*(c_+d_.*x_^2)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  c^p*Int[x^m*(1-I*a*x)^(p+I*n/2)*(1+I*a*x)^(p-I*n/2),x] /;
FreeQ[{a,c,d,m,n,p},x] && EqQ[d-a^2*c] && (IntegerQ[p] || PositiveQ[c])


Int[x_^m_.*(c_+d_.*x_^2)^p_*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
  c^(I*n/2)*Int[x^m*(c+d*x^2)^(p-I*n/2)*(1-I*a*x)^(I*n),x] /;
FreeQ[{a,c,d,m,p},x] && EqQ[d-a^2*c] && Not[IntegerQ[p] || PositiveQ[c]] && PositiveIntegerQ[I*n/2]


Int[x_^m_.*(c_+d_.*x_^2)^p_*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
  1/c^(I*n/2)*Int[x^m*(c+d*x^2)^(p+I*n/2)/(1+I*a*x)^(I*n),x] /;
FreeQ[{a,c,d,m,p},x] && EqQ[d-a^2*c] && Not[IntegerQ[p] || PositiveQ[c]] && NegativeIntegerQ[I*n/2]


Int[x_^m_.*(c_+d_.*x_^2)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  c^IntPart[p]*(c+d*x^2)^FracPart[p]/(1+a^2*x^2)^FracPart[p]*Int[x^m*(1+a^2*x^2)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,m,n,p},x] && EqQ[d-a^2*c] && Not[IntegerQ[p] || PositiveQ[c]]


Int[u_*(c_+d_.*x_^2)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  c^p*Int[u*(1-I*a*x)^(p+I*n/2)*(1+I*a*x)^(p-I*n/2),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[d-a^2*c] && (IntegerQ[p] || PositiveQ[c])


Int[u_*(c_+d_.*x_^2)^p_.*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
  c^IntPart[p]*(c+d*x^2)^FracPart[p]/((1-I*a*x)^FracPart[p]*(1+I*a*x)^FracPart[p])*
    Int[u*(1-I*a*x)^(p+I*n/2)*(1+I*a*x)^(p-I*n/2),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[d-a^2*c] && (IntegerQ[p] || PositiveQ[c]) && IntegerQ[I*n/2]


Int[u_*(c_+d_.*x_^2)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  c^IntPart[p]*(c+d*x^2)^FracPart[p]/(1+a^2*x^2)^FracPart[p]*Int[u*(1+a^2*x^2)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[d-a^2*c] && Not[IntegerQ[p] || PositiveQ[c]] && Not[IntegerQ[I*n/2]]


Int[u_.*(c_+d_./x_^2)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  d^p*Int[u/x^(2*p)*(1+a^2*x^2)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n},x] && EqQ[c-a^2*d] && IntegerQ[p]


Int[u_.*(c_+d_./x_^2)^p_*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
  c^p*Int[u*(1-I/(a*x))^p*(1+I/(a*x))^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,p},x] && EqQ[c-a^2*d] && Not[IntegerQ[p]] && IntegerQ[I*n/2] && PositiveQ[c]


Int[u_.*(c_+d_./x_^2)^p_*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
  x^(2*p)*(c+d/x^2)^p/((1-I*a*x)^p*(1+I*a*x)^p)*Int[u/x^(2*p)*(1-I*a*x)^p*(1+I*a*x)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[c-a^2*d] && Not[IntegerQ[p]] && IntegerQ[I*n/2] && Not[PositiveQ[c]]


Int[u_.*(c_+d_./x_^2)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
  x^(2*p)*(c+d/x^2)^p/(1+a^2*x^2)^p*Int[u/x^(2*p)*(1+a^2*x^2)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[c-a^2*d] && Not[IntegerQ[p]] && Not[IntegerQ[I*n/2]]


Int[E^(n_.*ArcTan[c_.*(a_+b_.*x_)]),x_Symbol] :=
  Int[(1-I*a*c-I*b*c*x)^(I*n/2)/(1+I*a*c+I*b*c*x)^(I*n/2),x] /;
FreeQ[{a,b,c,n},x]


Int[x_^m_*E^(n_*ArcTan[c_.*(a_+b_.*x_)]),x_Symbol] :=
  4/(I^m*n*b^(m+1)*c^(m+1))*
    Subst[Int[x^(2/(I*n))*(1-I*a*c-(1+I*a*c)*x^(2/(I*n)))^m/(1+x^(2/(I*n)))^(m+2),x],x,
      (1-I*c*(a+b*x))^(I*n/2)/(1+I*c*(a+b*x))^(I*n/2)] /;
FreeQ[{a,b,c},x] && NegativeIntegerQ[m] && RationalQ[I*n] && -1<I*n<1


Int[(d_.+e_.*x_)^m_.*E^(n_.*ArcTan[c_.*(a_+b_.*x_)]),x_Symbol] :=
  Int[(d+e*x)^m*(1-I*a*c-I*b*c*x)^(I*n/2)/(1+I*a*c+I*b*c*x)^(I*n/2),x] /;
FreeQ[{a,b,c,d,e,m,n},x]


Int[u_.*(c_+d_.*x_+e_.*x_^2)^p_.*E^(n_.*ArcTan[a_+b_.*x_]),x_Symbol] :=
  (c/(1+a^2))^p*Int[u*(1-I*a-I*b*x)^(p+I*n/2)*(1+I*a+I*b*x)^(p-I*n/2),x] /;
FreeQ[{a,b,c,d,e,n,p},x] && EqQ[b*d-2*a*e] && EqQ[b^2*c-e(1+a^2)] && (IntegerQ[p] || PositiveQ[c/(1+a^2)])


Int[u_.*(c_+d_.*x_+e_.*x_^2)^p_.*E^(n_.*ArcTan[a_+b_.*x_]),x_Symbol] :=
  (c+d*x+e*x^2)^p/(1+a^2+2*a*b*x+b^2*x^2)^p*Int[u*(1+a^2+2*a*b*x+b^2*x^2)^p*E^(n*ArcTan[a*x]),x] /;
FreeQ[{a,b,c,d,e,n,p},x] && EqQ[b*d-2*a*e] && EqQ[b^2*c-e(1+a^2)] && Not[IntegerQ[p] || PositiveQ[c/(1+a^2)]]


Int[u_.*E^(n_.*ArcTan[c_./(a_.+b_.*x_)]),x_Symbol] :=
  Int[u*E^(n*ArcCot[a/c+b*x/c]),x] /;
FreeQ[{a,b,c,n},x]


Int[u_.*E^(n_*ArcCot[a_.*x_]),x_Symbol] :=
  (-1)^(I*n/2)*Int[u*E^(-n*ArcTan[a*x]),x] /;
FreeQ[a,x] && IntegerQ[I*n/2]


Int[E^(n_*ArcCot[a_.*x_]),x_Symbol] :=
  -Subst[Int[(1-I*x/a)^((I*n+1)/2)/(x^2*(1+I*x/a)^((I*n-1)/2)*Sqrt[1+x^2/a^2]),x],x,1/x] /;
FreeQ[a,x] && OddQ[I*n]


Int[x_^m_.*E^(n_*ArcCot[a_.*x_]),x_Symbol] :=
  -Subst[Int[(1-I*x/a)^((I*n+1)/2)/(x^(m+2)*(1+I*x/a)^((I*n-1)/2)*Sqrt[1+x^2/a^2]),x],x,1/x] /;
FreeQ[a,x] && OddQ[I*n] && IntegerQ[m]


Int[E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  -Subst[Int[(1-I*x/a)^(I*n/2)/(x^2*(1+I*x/a)^(I*n/2)),x],x,1/x] /;
FreeQ[{a,n},x] && Not[IntegerQ[I*n]]


Int[x_^m_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  -Subst[Int[(1-I*x/a)^(n/2)/(x^(m+2)*(1+I*x/a)^(n/2)),x],x,1/x] /;
FreeQ[{a,n},x] && Not[IntegerQ[I*n]] && IntegerQ[m]


Int[x_^m_*E^(n_*ArcCot[a_.*x_]),x_Symbol] :=
  -x^m*(1/x)^m*Subst[Int[(1-I*x/a)^((I*n+1)/2)/(x^(m+2)*(1+I*x/a)^((I*n-1)/2)*Sqrt[1+x^2/a^2]),x],x,1/x] /;
FreeQ[{a,m},x] && OddQ[I*n] && Not[IntegerQ[m]]


Int[x_^m_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  -Subst[Int[(1-I*x/a)^(n/2)/(x^(m+2)*(1+I*x/a)^(n/2)),x],x,1/x] /;
FreeQ[{a,m,n},x] && Not[IntegerQ[I*n/2]] && Not[IntegerQ[m]]


Int[u_.*(c_+d_.*x_)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  d^p*Int[u*x^p*(1+c/(d*x))^p*E^(n*ArcCot[a*x]),x] /;
FreeQ[{a,c,d,n},x] && EqQ[a^2*c^2+d^2] && Not[IntegerQ[I*n/2]] && IntegerQ[p]


Int[u_.*(c_+d_.*x_)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  (c+d*x)^p/(x^p*(1+c/(d*x))^p)*Int[u*x^p*(1+c/(d*x))^p*E^(n*ArcCot[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[a^2*c^2+d^2] && Not[IntegerQ[I*n/2]] && Not[IntegerQ[p]]


Int[(c_+d_./x_)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  -c^p*Subst[Int[(1+d*x/c)^p*(1-I*x/a)^(I*n/2)/(x^2*(1+I*x/a)^(I*n/2)),x],x,1/x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[c^2+a^2*d^2] && Not[IntegerQ[I*n/2]] && (IntegerQ[p] || PositiveQ[c])


Int[x_^m_.*(c_+d_./x_)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  -c^p*Subst[Int[(1+d*x/c)^p*(1-I*x/a)^(I*n/2)/(x^(m+2)*(1+I*x/a)^(I*n/2)),x],x,1/x] /;
FreeQ[{a,c,d,m,n,p},x] && EqQ[c^2+a^2*d^2] && Not[IntegerQ[I*n/2]] && (IntegerQ[p] || PositiveQ[c]) && IntegerQ[m]


Int[(c_+d_./x_)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  (c+d/x)^p/(1+d/(c*x))^p*Int[(1+d/(c*x))^p*E^(n*ArcCot[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[c^2+a^2*d^2] && Not[IntegerQ[I*n/2]] && Not[IntegerQ[p] || PositiveQ[c]]


Int[x_^m_*(c_+d_./x_)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  -c^p*x^m*(1/x)^m*Subst[Int[(1+d*x/c)^p*(1-I*x/a)^(I*n/2)/(x^(m+2)*(1+I*x/a)^(I*n/2)),x],x,1/x] /;
FreeQ[{a,c,d,m,n,p},x] && EqQ[c^2+a^2*d^2] && Not[IntegerQ[I*n/2]] && (IntegerQ[p] || PositiveQ[c]) && Not[IntegerQ[m]]


Int[u_.*(c_+d_./x_)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  (c+d/x)^p/(1+d/(c*x))^p*Int[u*(1+d/(c*x))^p*E^(n*ArcCot[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[c^2+a^2*d^2] && Not[IntegerQ[I*n/2]] && Not[IntegerQ[p] || PositiveQ[c]]


Int[E^(n_.*ArcCot[a_.*x_])/(c_+d_.*x_^2),x_Symbol] :=
  -E^(n*ArcCot[a*x])/(a*c*n) /;
FreeQ[{a,c,d,n},x] && EqQ[d-a^2*c]


Int[E^(n_.*ArcCot[a_.*x_])/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  -(n-a*x)*E^(n*ArcCot[a*x])/(a*c*(n^2+1)*Sqrt[c+d*x^2]) /;
FreeQ[{a,c,d,n},x] && EqQ[d-a^2*c] && Not[OddQ[I*n]]


Int[(c_+d_.*x_^2)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  -(n+2*a*(p+1)*x)*(c+d*x^2)^(p+1)*E^(n*ArcCot[a*x])/(a*c*(n^2+4*(p+1)^2)) + 
  2*(p+1)*(2*p+3)/(c*(n^2+4*(p+1)^2))*Int[(c+d*x^2)^(p+1)*E^(n*ArcCot[a*x]),x] /;
FreeQ[{a,c,d,n},x] && EqQ[d-a^2*c] && RationalQ[p] && p<-1 && p!=-3/2 && NeQ[n^2+4*(p+1)^2] && 
  Not[IntegerQ[p] && EvenQ[I*n]] && Not[Not[IntegerQ[p]] && OddQ[I*n]]


Int[x_*E^(n_.*ArcCot[a_.*x_])/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  -(1+a*n*x)*E^(n*ArcCot[a*x])/(a^2*c*(n^2+1)*Sqrt[c+d*x^2]) /;
FreeQ[{a,c,d,n},x] && EqQ[d-a^2*c] && Not[OddQ[I*n]]


Int[x_*(c_+d_.*x_^2)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  (2*(p+1)-a*n*x)*(c+d*x^2)^(p+1)*E^(n*ArcCot[a*x])/(a^2*c*(n^2+4*(p+1)^2)) + 
  n*(2*p+3)/(a*c*(n^2+4*(p+1)^2))*Int[(c+d*x^2)^(p+1)*E^(n*ArcCot[a*x]),x] /;
FreeQ[{a,c,d,n},x] && EqQ[d-a^2*c] && RationalQ[p] && p<=-1 && p!=-3/2 && NeQ[n^2+4*(p+1)^2] && 
  Not[IntegerQ[p] && EvenQ[I*n]] && Not[Not[IntegerQ[p]] && OddQ[I*n]]


Int[x_^2*(c_+d_.*x_^2)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  (n+2*(p+1)*a*x)*(c+d*x^2)^(p+1)*E^(n*ArcCot[a*x])/(a^3*c*n^2*(n^2+1)) /;
FreeQ[{a,c,d,n},x] && EqQ[d-a^2*c] && EqQ[n^2-2*(p+1)] && NeQ[n^2+1]


Int[x_^2*(c_+d_.*x_^2)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  (n+2*(p+1)*a*x)*(c+d*x^2)^(p+1)*E^(n*ArcCot[a*x])/(a^3*c*(n^2+4*(p+1)^2)) + 
  (n^2-2*(p+1))/(a^2*c*(n^2+4*(p+1)^2))*Int[(c+d*x^2)^(p+1)*E^(n*ArcCot[a*x]),x] /;
FreeQ[{a,c,d,n},x] && EqQ[d-a^2*c] && RationalQ[p] && p<=-1 && NeQ[n^2-2*(p+1)] && NeQ[n^2+4*(p+1)^2] && 
  Not[IntegerQ[p] && EvenQ[I*n]] && Not[Not[IntegerQ[p]] && OddQ[I*n]]


Int[x_^m_.*(c_+d_.*x_^2)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  -c^p/a^(m+1)*Subst[Int[E^(n*x)*Cot[x]^(m+2*(p+1))/Cos[x]^(2*(p+1)),x],x,ArcCot[a*x]] /;
FreeQ[{a,c,d,n},x] && EqQ[d-a^2*c] && IntegerQ[m] && 3<=m<=-2(p+1) && IntegerQ[p]


Int[u_.*(c_+d_.*x_^2)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  d^p*Int[u*x^(2*p)*(1+1/(a^2*x^2))^p*E^(n*ArcCot[a*x]),x] /;
FreeQ[{a,c,d,n},x] && EqQ[d-a^2*c] && Not[IntegerQ[I*n/2]] && IntegerQ[p]


Int[u_.*(c_+d_.*x_^2)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  (c+d*x^2)^p/(x^(2*p)*(1+1/(a^2*x^2))^p)*Int[u*x^(2*p)*(1+1/(a^2*x^2))^p*E^(n*ArcCot[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[d-a^2*c] && Not[IntegerQ[I*n/2]] && Not[IntegerQ[p]]


Int[u_.*(c_+d_./x_^2)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  c^p/(I*a)^(2*p)*Int[u/x^(2*p)*(-1+I*a*x)^(p-I*n/2)*(1+I*a*x)^(p+I*n/2),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[c-a^2*d] && Not[IntegerQ[I*n/2]] && (IntegerQ[p] || PositiveQ[c]) && IntegersQ[2*p,p+I*n/2]


Int[(c_+d_./x_^2)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  -c^p*Subst[Int[(1-I*x/a)^(p+I*n/2)*(1+I*x/a)^(p-I*n/2)/x^2,x],x,1/x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[c-a^2*d] && Not[IntegerQ[I*n/2]] && (IntegerQ[p] || PositiveQ[c]) && Not[IntegersQ[2*p,p+I*n/2]]


Int[x_^m_.*(c_+d_./x_^2)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  -c^p*Subst[Int[(1-I*x/a)^(p+I*n/2)*(1+I*x/a)^(p-I*n/2)/x^(m+2),x],x,1/x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[c-a^2*d] && Not[IntegerQ[I*n/2]] && (IntegerQ[p] || PositiveQ[c]) && Not[IntegersQ[2*p,p+I*n/2]] && 
  IntegerQ[m]


Int[x_^m_*(c_+d_./x_^2)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  -c^p*x^m*(1/x)^m*Subst[Int[(1-I*x/a)^(p+I*n/2)*(1+I*x/a)^(p-I*n/2)/x^(m+2),x],x,1/x] /;
FreeQ[{a,c,d,m,n,p},x] && EqQ[c-a^2*d] && Not[IntegerQ[I*n/2]] && (IntegerQ[p] || PositiveQ[c]) && Not[IntegersQ[2*p,p+I*n/2]] && 
  Not[IntegerQ[m]]


Int[u_.*(c_+d_./x_^2)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
  (c+d/x^2)^p/(1+1/(a^2*x^2))^p*Int[u*(1+1/(a^2*x^2))^p*E^(n*ArcCot[a*x]),x] /;
FreeQ[{a,c,d,n,p},x] && EqQ[c-a^2*d] && Not[IntegerQ[I*n/2]] && Not[IntegerQ[p] || PositiveQ[c]]


Int[u_.*E^(n_*ArcCot[c_.*(a_+b_.*x_)]),x_Symbol] :=
  (-1)^(I*n/2)*Int[u*E^(-n*ArcTan[c*(a+b*x)]),x] /;
FreeQ[{a,b,c},x] && IntegerQ[I*n/2]


Int[E^(n_.*ArcCot[c_.*(a_+b_.*x_)]),x_Symbol] :=
  (I*c*(a+b*x))^(I*n/2)*(1+1/(I*c*(a+b*x)))^(I*n/2)/(1+I*a*c+I*b*c*x)^(I*n/2)*
    Int[(1+I*a*c+I*b*c*x)^(I*n/2)/(-1+I*a*c+I*b*c*x)^(I*n/2),x] /;
FreeQ[{a,b,c,n},x] && Not[IntegerQ[I*n/2]]


Int[x_^m_*E^(n_*ArcCoth[c_.*(a_+b_.*x_)]),x_Symbol] :=
  4/(I^m*n*b^(m+1)*c^(m+1))*
    Subst[Int[x^(2/(I*n))*(1+I*a*c+(1-I*a*c)*x^(2/(I*n)))^m/(-1+x^(2/(I*n)))^(m+2),x],x,
      (1+1/(I*c*(a+b*x)))^(I*n/2)/(1-1/(I*c*(a+b*x)))^(I*n/2)] /;
FreeQ[{a,b,c},x] && NegativeIntegerQ[m] && RationalQ[I*n] && -1<I*n<1


Int[(d_.+e_.*x_)^m_.*E^(n_.*ArcCoth[c_.*(a_+b_.*x_)]),x_Symbol] :=
  (I*c*(a+b*x))^(I*n/2)*(1+1/(I*c*(a+b*x)))^(I*n/2)/(1+I*a*c+I*b*c*x)^(I*n/2)*
    Int[(d+e*x)^m*(1+I*a*c+I*b*c*x)^(I*n/2)/(-1+I*a*c+I*b*c*x)^(I*n/2),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && Not[IntegerQ[I*n/2]]


Int[u_.*(c_+d_.*x_+e_.*x_^2)^p_.*E^(n_.*ArcCot[a_+b_.*x_]),x_Symbol] :=
  (c/(1+a^2))^p*((I*a+I*b*x)/(1+I*a+I*b*x))^(I*n/2)*((1+I*a+I*b*x)/(I*a+I*b*x))^(I*n/2)*
    ((1-I*a-I*b*x)^(I*n/2)/(-1+I*a+I*b*x)^(I*n/2))*
    Int[u*(1-I*a-I*b*x)^(p-I*n/2)*(1+I*a+I*b*x)^(p+I*n/2),x] /;
FreeQ[{a,b,c,d,e,n,p},x] && Not[IntegerQ[I*n/2]] && EqQ[b*d-2*a*e] && EqQ[b^2*c-e(1+a^2)] && 
  (IntegerQ[p] || PositiveQ[c/(1+a^2)])


Int[u_.*(c_+d_.*x_+e_.*x_^2)^p_.*E^(n_.*ArcCot[a_+b_.*x_]),x_Symbol] :=
  (c+d*x+e*x^2)^p/(1+a^2+2*a*b*x+b^2*x^2)^p*Int[u*(1+a^2+2*a*b*x+b^2*x^2)^p*E^(n*ArcCot[a*x]),x] /;
FreeQ[{a,b,c,d,e,n,p},x] && Not[IntegerQ[I*n/2]] && EqQ[b*d-2*a*e] && EqQ[b^2*c-e(1+a^2)] && 
  Not[IntegerQ[p] || PositiveQ[c/(1+a^2)]]


Int[u_.*E^(n_.*ArcCot[c_./(a_.+b_.*x_)]),x_Symbol] :=
  Int[u*E^(n*ArcTan[a/c+b*x/c]),x] /;
FreeQ[{a,b,c,n},x]





(* ::Subsection::Closed:: *)
(*5.2.3 Miscellaneous inverse tangent*)
(**)


Int[(a_.+b_.*ArcTan[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[(a+b*ArcTan[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d},x] && PositiveIntegerQ[n]


Int[(a_.+b_.*ArcCot[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[(a+b*ArcCot[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d},x] && PositiveIntegerQ[n]


Int[(a_.+b_.*ArcTan[c_+d_.*x_])^n_,x_Symbol] :=
  Defer[Int][(a+b*ArcTan[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && Not[PositiveIntegerQ[n]]


Int[(a_.+b_.*ArcCot[c_+d_.*x_])^n_,x_Symbol] :=
  Defer[Int][(a+b*ArcCot[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && Not[PositiveIntegerQ[n]]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcTan[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[((d*e-c*f)/d+f*x/d)^m*(a+b*ArcTan[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && PositiveIntegerQ[n]


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCot[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[((d*e-c*f)/d+f*x/d)^m*(a+b*ArcCot[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && PositiveIntegerQ[n]


Int[(e_.+f_.*x_)^m_*(a_.+b_.*ArcTan[c_+d_.*x_])^n_,x_Symbol] :=
  Defer[Int][(e+f*x)^m*(a+b*ArcTan[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && Not[PositiveIntegerQ[n]]


Int[(e_.+f_.*x_)^m_*(a_.+b_.*ArcCot[c_+d_.*x_])^n_,x_Symbol] :=
  Defer[Int][(e+f*x)^m*(a+b*ArcCot[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && Not[PositiveIntegerQ[n]]


Int[(A_.+B_.*x_+C_.*x_^2)^p_.*(a_.+b_.*ArcTan[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[(C/d^2+C/d^2*x^2)^p*(a+b*ArcTan[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,A,B,C,n,p},x] && EqQ[B*(1+c^2)-2*A*c*d] && EqQ[2*c*C-B*d]


Int[(A_.+B_.*x_+C_.*x_^2)^p_.*(a_.+b_.*ArcCot[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[(C/d^2+C/d^2*x^2)^p*(a+b*ArcCot[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,A,B,C,n,p},x] && EqQ[B*(1+c^2)-2*A*c*d] && EqQ[2*c*C-B*d]


Int[(e_.+f_.*x_)^m_.*(A_.+B_.*x_+C_.*x_^2)^p_.*(a_.+b_.*ArcTan[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[((d*e-c*f)/d+f*x/d)^m*(C/d^2+C/d^2*x^2)^p*(a+b*ArcTan[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m,n,p},x] && EqQ[B*(1+c^2)-2*A*c*d] && EqQ[2*c*C-B*d]


Int[(e_.+f_.*x_)^m_.*(A_.+B_.*x_+C_.*x_^2)^p_.*(a_.+b_.*ArcCot[c_+d_.*x_])^n_.,x_Symbol] :=
  1/d*Subst[Int[((d*e-c*f)/d+f*x/d)^m*(C/d^2+C/d^2*x^2)^p*(a+b*ArcCot[x])^n,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m,n,p},x] && EqQ[B*(1+c^2)-2*A*c*d] && EqQ[2*c*C-B*d]


Int[ArcTan[a_+b_.*x_]/(c_+d_.*x_^n_.),x_Symbol] :=
  I/2*Int[Log[1-I*a-I*b*x]/(c+d*x^n),x] -
  I/2*Int[Log[1+I*a+I*b*x]/(c+d*x^n),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[n]


Int[ArcCot[a_+b_.*x_]/(c_+d_.*x_^n_.),x_Symbol] :=
  I/2*Int[Log[(-I+a+b*x)/(a+b*x)]/(c+d*x^n),x] -
  I/2*Int[Log[(I+a+b*x)/(a+b*x)]/(c+d*x^n),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[n]


Int[ArcTan[a_+b_.*x_]/(c_+d_.*x_^n_),x_Symbol] :=
  Defer[Int][ArcTan[a+b*x]/(c+d*x^n),x] /;
FreeQ[{a,b,c,d,n},x] && Not[RationalQ[n]]


Int[ArcCot[a_+b_.*x_]/(c_+d_.*x_^n_),x_Symbol] :=
  Defer[Int][ArcCot[a+b*x]/(c+d*x^n),x] /;
FreeQ[{a,b,c,d,n},x] && Not[RationalQ[n]]


Int[ArcTan[a_+b_.*x_^n_],x_Symbol] :=
  x*ArcTan[a+b*x^n] -
  b*n*Int[x^n/(1+a^2+2*a*b*x^n+b^2*x^(2*n)),x] /;
FreeQ[{a,b,n},x]


Int[ArcCot[a_+b_.*x_^n_],x_Symbol] :=
  x*ArcCot[a+b*x^n] +
  b*n*Int[x^n/(1+a^2+2*a*b*x^n+b^2*x^(2*n)),x] /;
FreeQ[{a,b,n},x]


Int[ArcTan[a_.+b_.*x_^n_]/x_,x_Symbol] :=
  I/2*Int[Log[1-I*a-I*b*x^n]/x,x] -
  I/2*Int[Log[1+I*a+I*b*x^n]/x,x] /;
FreeQ[{a,b,n},x]


Int[ArcCot[a_.+b_.*x_^n_]/x_,x_Symbol] :=
  I/2*Int[Log[1-I/(a+b*x^n)]/x,x] -
  I/2*Int[Log[1+I/(a+b*x^n)]/x,x] /;
FreeQ[{a,b,n},x]


Int[x_^m_.*ArcTan[a_+b_.*x_^n_],x_Symbol] :=
  x^(m+1)*ArcTan[a+b*x^n]/(m+1) -
  b*n/(m+1)*Int[x^(m+n)/(1+a^2+2*a*b*x^n+b^2*x^(2*n)),x] /;
FreeQ[{a,b},x] && RationalQ[m,n] && m+1!=0 && m+1!=n


Int[x_^m_.*ArcCot[a_+b_.*x_^n_],x_Symbol] :=
  x^(m+1)*ArcCot[a+b*x^n]/(m+1) +
  b*n/(m+1)*Int[x^(m+n)/(1+a^2+2*a*b*x^n+b^2*x^(2*n)),x] /;
FreeQ[{a,b},x] && RationalQ[m,n] && m+1!=0 && m+1!=n


Int[ArcTan[a_.+b_.*f_^(c_.+d_.*x_)],x_Symbol] :=
  I/2*Int[Log[1-I*a-I*b*f^(c+d*x)],x] -
  I/2*Int[Log[1+I*a+I*b*f^(c+d*x)],x] /;
FreeQ[{a,b,c,d,f},x]


Int[ArcCot[a_.+b_.*f_^(c_.+d_.*x_)],x_Symbol] :=
  I/2*Int[Log[1-I/(a+b*f^(c+d*x))],x] -
  I/2*Int[Log[1+I/(a+b*f^(c+d*x))],x] /;
FreeQ[{a,b,c,d,f},x] 


Int[x_^m_.*ArcTan[a_.+b_.*f_^(c_.+d_.*x_)],x_Symbol] :=
  I/2*Int[x^m*Log[1-I*a-I*b*f^(c+d*x)],x] -
  I/2*Int[x^m*Log[1+I*a+I*b*f^(c+d*x)],x] /;
FreeQ[{a,b,c,d,f},x] && IntegerQ[m] && m>0


Int[x_^m_.*ArcCot[a_.+b_.*f_^(c_.+d_.*x_)],x_Symbol] :=
  I/2*Int[x^m*Log[1-I/(a+b*f^(c+d*x))],x] -
  I/2*Int[x^m*Log[1+I/(a+b*f^(c+d*x))],x] /;
FreeQ[{a,b,c,d,f},x] && IntegerQ[m] && m>0


Int[u_.*ArcTan[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
  Int[u*ArcCot[a/c+b*x^n/c]^m,x] /;
FreeQ[{a,b,c,n,m},x]


Int[u_.*ArcCot[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
  Int[u*ArcTan[a/c+b*x^n/c]^m,x] /;
FreeQ[{a,b,c,n,m},x]


Int[1/(Sqrt[a_.+b_.*x_^2]*ArcTan[c_.*x_/Sqrt[a_.+b_.*x_^2]]),x_Symbol] :=
  1/c*Log[ArcTan[c*x/Sqrt[a+b*x^2]]] /;
FreeQ[{a,b,c},x] && EqQ[b+c^2]


Int[1/(Sqrt[a_.+b_.*x_^2]*ArcCot[c_.*x_/Sqrt[a_.+b_.*x_^2]]),x_Symbol] :=
  -1/c*Log[ArcCot[c*x/Sqrt[a+b*x^2]]] /;
FreeQ[{a,b,c},x] && EqQ[b+c^2]


Int[ArcTan[c_.*x_/Sqrt[a_.+b_.*x_^2]]^m_./Sqrt[a_.+b_.*x_^2],x_Symbol] :=
  ArcTan[c*x/Sqrt[a+b*x^2]]^(m+1)/(c*(m+1)) /;
FreeQ[{a,b,c,m},x] && EqQ[b+c^2] && NeQ[m+1]


Int[ArcCot[c_.*x_/Sqrt[a_.+b_.*x_^2]]^m_./Sqrt[a_.+b_.*x_^2],x_Symbol] :=
  -ArcCot[c*x/Sqrt[a+b*x^2]]^(m+1)/(c*(m+1)) /;
FreeQ[{a,b,c,m},x] && EqQ[b+c^2] && NeQ[m+1]


Int[ArcTan[c_.*x_/Sqrt[a_.+b_.*x_^2]]^m_./Sqrt[d_.+e_.*x_^2],x_Symbol] :=
  Sqrt[a+b*x^2]/Sqrt[d+e*x^2]*Int[ArcTan[c*x/Sqrt[a+b*x^2]]^m/Sqrt[a+b*x^2],x] /;
FreeQ[{a,b,c,d,e,m},x] && EqQ[b+c^2] && EqQ[b*d-a*e]


Int[ArcCot[c_.*x_/Sqrt[a_.+b_.*x_^2]]^m_./Sqrt[d_.+e_.*x_^2],x_Symbol] :=
  Sqrt[a+b*x^2]/Sqrt[d+e*x^2]*Int[ArcCot[c*x/Sqrt[a+b*x^2]]^m/Sqrt[a+b*x^2],x] /;
FreeQ[{a,b,c,d,e,m},x] && EqQ[b+c^2] && EqQ[b*d-a*e]


Int[u_.*ArcTan[v_+s_.*Sqrt[w_]],x_Symbol] :=
  Pi*s/4*Int[u,x] + 1/2*Int[u*ArcTan[v],x] /;
EqQ[s^2-1] && EqQ[w-(v^2+1)]


Int[u_.*ArcCot[v_+s_.*Sqrt[w_]],x_Symbol] :=
  Pi*s/4*Int[u,x] - 1/2*Int[u*ArcTan[v],x] /;
EqQ[s^2-1] && EqQ[w-(v^2+1)]


If[ShowSteps,

Int[u_*v_^n_.,x_Symbol] :=
  With[{tmp=InverseFunctionOfLinear[u,x]},
  ShowStep["","Int[f[x,ArcTan[a+b*x]]/(1+(a+b*x)^2),x]",
		   "Subst[Int[f[-a/b+Tan[x]/b,x],x],x,ArcTan[a+b*x]]/b",Hold[
  (-Discriminant[v,x]/(4*Coefficient[v,x,2]))^n/Coefficient[tmp[[1]],x,1]*
	Subst[Int[SimplifyIntegrand[SubstForInverseFunction[u,tmp,x]*Sec[x]^(2*(n+1)),x],x], x, tmp]]] /;
 Not[FalseQ[tmp]] && Head[tmp]===ArcTan && EqQ[Discriminant[v,x]*tmp[[1]]^2+D[v,x]^2]] /;
SimplifyFlag && QuadraticQ[v,x] && IntegerQ[n] && n<0 && NegQ[Discriminant[v,x]] && MatchQ[u,r_.*f_^w_ /; FreeQ[f,x]],

Int[u_*v_^n_.,x_Symbol] :=
  With[{tmp=InverseFunctionOfLinear[u,x]},
  (-Discriminant[v,x]/(4*Coefficient[v,x,2]))^n/Coefficient[tmp[[1]],x,1]*
	Subst[Int[SimplifyIntegrand[SubstForInverseFunction[u,tmp,x]*Sec[x]^(2*(n+1)),x],x], x, tmp] /;
 Not[FalseQ[tmp]] && Head[tmp]===ArcTan && EqQ[Discriminant[v,x]*tmp[[1]]^2+D[v,x]^2]] /;
QuadraticQ[v,x] && IntegerQ[n] && n<0 && NegQ[Discriminant[v,x]] && MatchQ[u,r_.*f_^w_ /; FreeQ[f,x]]]


If[ShowSteps,

Int[u_*v_^n_.,x_Symbol] :=
  With[{tmp=InverseFunctionOfLinear[u,x]},
  ShowStep["","Int[f[x,ArcCot[a+b*x]]/(1+(a+b*x)^2),x]",
		   "-Subst[Int[f[-a/b+Cot[x]/b,x],x],x,ArcCot[a+b*x]]/b",Hold[
  -(-Discriminant[v,x]/(4*Coefficient[v,x,2]))^n/Coefficient[tmp[[1]],x,1]*
	Subst[Int[SimplifyIntegrand[SubstForInverseFunction[u,tmp,x]*Csc[x]^(2*(n+1)),x],x], x, tmp]]] /;
 Not[FalseQ[tmp]] && Head[tmp]===ArcCot && EqQ[Discriminant[v,x]*tmp[[1]]^2+D[v,x]^2]] /;
SimplifyFlag && QuadraticQ[v,x] && IntegerQ[n] && n<0 && NegQ[Discriminant[v,x]] && MatchQ[u,r_.*f_^w_ /; FreeQ[f,x]],

Int[u_*v_^n_.,x_Symbol] :=
  With[{tmp=InverseFunctionOfLinear[u,x]},
  -(-Discriminant[v,x]/(4*Coefficient[v,x,2]))^n/Coefficient[tmp[[1]],x,1]*
	Subst[Int[SimplifyIntegrand[SubstForInverseFunction[u,tmp,x]*Csc[x]^(2*(n+1)),x],x], x, tmp] /;
 Not[FalseQ[tmp]] && Head[tmp]===ArcCot && EqQ[Discriminant[v,x]*tmp[[1]]^2+D[v,x]^2]] /;
QuadraticQ[v,x] && IntegerQ[n] && n<0 && NegQ[Discriminant[v,x]] && MatchQ[u,r_.*f_^w_ /; FreeQ[f,x]]]


Int[ArcTan[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTan[c+d*Tan[a+b*x]] - 
  I*b*Int[x/(c+I*d+c*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && EqQ[(c+I*d)^2+1]


Int[ArcCot[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCot[c+d*Tan[a+b*x]] + 
  I*b*Int[x/(c+I*d+c*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && EqQ[(c+I*d)^2+1]


Int[ArcTan[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTan[c+d*Cot[a+b*x]] - 
  I*b*Int[x/(c-I*d-c*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && EqQ[(c-I*d)^2+1]


Int[ArcCot[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCot[c+d*Cot[a+b*x]] + 
  I*b*Int[x/(c-I*d-c*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && EqQ[(c-I*d)^2+1]


Int[ArcTan[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTan[c+d*Tan[a+b*x]] - 
  b*(1+I*c+d)*Int[x*E^(2*I*a+2*I*b*x)/(1+I*c-d+(1+I*c+d)*E^(2*I*a+2*I*b*x)),x] + 
  b*(1-I*c-d)*Int[x*E^(2*I*a+2*I*b*x)/(1-I*c+d+(1-I*c-d)*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NeQ[(c+I*d)^2+1]


Int[ArcCot[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCot[c+d*Tan[a+b*x]] + 
  b*(1+I*c+d)*Int[x*E^(2*I*a+2*I*b*x)/(1+I*c-d+(1+I*c+d)*E^(2*I*a+2*I*b*x)),x] - 
  b*(1-I*c-d)*Int[x*E^(2*I*a+2*I*b*x)/(1-I*c+d+(1-I*c-d)*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NeQ[(c+I*d)^2+1]


Int[ArcTan[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTan[c+d*Cot[a+b*x]] + 
  b*(1+I*c-d)*Int[x*E^(2*I*a+2*I*b*x)/(1+I*c+d-(1+I*c-d)*E^(2*I*a+2*I*b*x)),x] - 
  b*(1-I*c+d)*Int[x*E^(2*I*a+2*I*b*x)/(1-I*c-d-(1-I*c+d)*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NeQ[(c+I*d)^2+1]


Int[ArcCot[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCot[c+d*Cot[a+b*x]] - 
  b*(1+I*c-d)*Int[x*E^(2*I*a+2*I*b*x)/(1+I*c+d-(1+I*c-d)*E^(2*I*a+2*I*b*x)),x] + 
  b*(1-I*c+d)*Int[x*E^(2*I*a+2*I*b*x)/(1-I*c-d-(1-I*c+d)*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NeQ[(c-I*d)^2+1]


Int[(e_.+f_.*x_)^m_.*ArcTan[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcTan[c+d*Tan[a+b*x]]/(f*(m+1)) - 
  I*b/(f*(m+1))*Int[(e+f*x)^(m+1)/(c+I*d+c*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveIntegerQ[m] && EqQ[(c+I*d)^2+1]


Int[(e_.+f_.*x_)^m_.*ArcCot[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcCot[c+d*Tan[a+b*x]]/(f*(m+1)) + 
  I*b/(f*(m+1))*Int[(e+f*x)^(m+1)/(c+I*d+c*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveIntegerQ[m] && EqQ[(c+I*d)^2+1]


Int[(e_.+f_.*x_)^m_.*ArcTan[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcTan[c+d*Cot[a+b*x]]/(f*(m+1)) - 
  I*b/(f*(m+1))*Int[(e+f*x)^(m+1)/(c-I*d-c*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveIntegerQ[m] && EqQ[(c-I*d)^2+1]


Int[(e_.+f_.*x_)^m_.*ArcCot[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcCot[c+d*Cot[a+b*x]]/(f*(m+1)) + 
  I*b/(f*(m+1))*Int[(e+f*x)^(m+1)/(c-I*d-c*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveIntegerQ[m] && EqQ[(c-I*d)^2+1]


Int[(e_.+f_.*x_)^m_.*ArcTan[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcTan[c+d*Tan[a+b*x]]/(f*(m+1)) - 
  b*(1+I*c+d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*I*a+2*I*b*x)/(1+I*c-d+(1+I*c+d)*E^(2*I*a+2*I*b*x)),x] + 
  b*(1-I*c-d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*I*a+2*I*b*x)/(1-I*c+d+(1-I*c-d)*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveIntegerQ[m] && NeQ[(c+I*d)^2+1]


Int[(e_.+f_.*x_)^m_.*ArcCot[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcCot[c+d*Tan[a+b*x]]/(f*(m+1)) + 
  b*(1+I*c+d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*I*a+2*I*b*x)/(1+I*c-d+(1+I*c+d)*E^(2*I*a+2*I*b*x)),x] - 
  b*(1-I*c-d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*I*a+2*I*b*x)/(1-I*c+d+(1-I*c-d)*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveIntegerQ[m] && NeQ[(c+I*d)^2+1]


Int[(e_.+f_.*x_)^m_.*ArcTan[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcTan[c+d*Cot[a+b*x]]/(f*(m+1)) + 
  b*(1+I*c-d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*I*a+2*I*b*x)/(1+I*c+d-(1+I*c-d)*E^(2*I*a+2*I*b*x)),x] - 
  b*(1-I*c+d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*I*a+2*I*b*x)/(1-I*c-d-(1-I*c+d)*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveIntegerQ[m] && NeQ[(c-I*d)^2+1]


Int[(e_.+f_.*x_)^m_.*ArcCot[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcCot[c+d*Cot[a+b*x]]/(f*(m+1)) - 
  b*(1+I*c-d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*I*a+2*I*b*x)/(1+I*c+d-(1+I*c-d)*E^(2*I*a+2*I*b*x)),x] + 
  b*(1-I*c+d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*I*a+2*I*b*x)/(1-I*c-d-(1-I*c+d)*E^(2*I*a+2*I*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveIntegerQ[m] && NeQ[(c-I*d)^2+1]


Int[ArcTan[Tanh[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTan[Tanh[a+b*x]] - b*Int[x*Sech[2*a+2*b*x],x] /;
FreeQ[{a,b},x]


Int[ArcCot[Tanh[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCot[Tanh[a+b*x]] + b*Int[x*Sech[2*a+2*b*x],x] /;
FreeQ[{a,b},x]


Int[ArcTan[Coth[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTan[Coth[a+b*x]] + b*Int[x*Sech[2*a+2*b*x],x] /;
FreeQ[{a,b},x]


Int[ArcCot[Coth[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCot[Coth[a+b*x]] - b*Int[x*Sech[2*a+2*b*x],x] /;
FreeQ[{a,b},x]


Int[(e_.+f_.*x_)^m_.*ArcTan[Tanh[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcTan[Tanh[a+b*x]]/(f*(m+1)) - b/(f*(m+1))*Int[(e+f*x)^(m+1)*Sech[2*a+2*b*x],x] /;
FreeQ[{a,b,e,f},x] && PositiveIntegerQ[m]


Int[(e_.+f_.*x_)^m_.*ArcCot[Tanh[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcCot[Tanh[a+b*x]]/(f*(m+1)) + b/(f*(m+1))*Int[(e+f*x)^(m+1)*Sech[2*a+2*b*x],x] /;
FreeQ[{a,b,e,f},x] && PositiveIntegerQ[m]


Int[(e_.+f_.*x_)^m_.*ArcTan[Coth[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcTan[Coth[a+b*x]]/(f*(m+1)) + b/(f*(m+1))*Int[(e+f*x)^(m+1)*Sech[2*a+2*b*x],x] /;
FreeQ[{a,b,e,f},x] && PositiveIntegerQ[m]


Int[(e_.+f_.*x_)^m_.*ArcCot[Coth[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcCot[Coth[a+b*x]]/(f*(m+1)) - b/(f*(m+1))*Int[(e+f*x)^(m+1)*Sech[2*a+2*b*x],x] /;
FreeQ[{a,b,e,f},x] && PositiveIntegerQ[m]


Int[ArcTan[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTan[c+d*Tanh[a+b*x]] - 
  b*Int[x/(c-d+c*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && EqQ[(c-d)^2+1]


Int[ArcCot[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCot[c+d*Tanh[a+b*x]] + 
  b*Int[x/(c-d+c*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && EqQ[(c-d)^2+1]


Int[ArcTan[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTan[c+d*Coth[a+b*x]] - 
  b*Int[x/(c-d-c*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && EqQ[(c-d)^2+1]


Int[ArcCot[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCot[c+d*Coth[a+b*x]] + 
  b*Int[x/(c-d-c*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && EqQ[(c-d)^2+1]


Int[ArcTan[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTan[c+d*Tanh[a+b*x]] + 
  I*b*(I-c-d)*Int[x*E^(2*a+2*b*x)/(I-c+d+(I-c-d)*E^(2*a+2*b*x)),x] - 
  I*b*(I+c+d)*Int[x*E^(2*a+2*b*x)/(I+c-d+(I+c+d)*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NeQ[(c-d)^2+1]


Int[ArcCot[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCot[c+d*Tanh[a+b*x]] - 
  I*b*(I-c-d)*Int[x*E^(2*a+2*b*x)/(I-c+d+(I-c-d)*E^(2*a+2*b*x)),x] + 
  I*b*(I+c+d)*Int[x*E^(2*a+2*b*x)/(I+c-d+(I+c+d)*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NeQ[(c-d)^2+1]


Int[ArcTan[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
  x*ArcTan[c+d*Coth[a+b*x]] - 
  I*b*(I-c-d)*Int[x*E^(2*a+2*b*x)/(I-c+d-(I-c-d)*E^(2*a+2*b*x)),x] + 
  I*b*(I+c+d)*Int[x*E^(2*a+2*b*x)/(I+c-d-(I+c+d)*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NeQ[(c-d)^2+1]


Int[ArcCot[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
  x*ArcCot[c+d*Coth[a+b*x]] + 
  I*b*(I-c-d)*Int[x*E^(2*a+2*b*x)/(I-c+d-(I-c-d)*E^(2*a+2*b*x)),x] - 
  I*b*(I+c+d)*Int[x*E^(2*a+2*b*x)/(I+c-d-(I+c+d)*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d},x] && NeQ[(c-d)^2+1]


Int[(e_.+f_.*x_)^m_.*ArcTan[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcTan[c+d*Tanh[a+b*x]]/(f*(m+1)) - 
  b/(f*(m+1))*Int[(e+f*x)^(m+1)/(c-d+c*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveIntegerQ[m] && EqQ[(c-d)^2+1]


Int[(e_.+f_.*x_)^m_.*ArcCot[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcCot[c+d*Tanh[a+b*x]]/(f*(m+1)) + 
  b/(f*(m+1))*Int[(e+f*x)^(m+1)/(c-d+c*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveIntegerQ[m] && EqQ[(c-d)^2+1]


Int[(e_.+f_.*x_)^m_.*ArcTan[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcTan[c+d*Coth[a+b*x]]/(f*(m+1)) - 
  b/(f*(m+1))*Int[(e+f*x)^(m+1)/(c-d-c*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveIntegerQ[m] && EqQ[(c-d)^2+1]


Int[(e_.+f_.*x_)^m_.*ArcCot[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcCot[c+d*Coth[a+b*x]]/(f*(m+1)) + 
  b/(f*(m+1))*Int[(e+f*x)^(m+1)/(c-d-c*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveIntegerQ[m] && EqQ[(c-d)^2+1]


Int[(e_.+f_.*x_)^m_.*ArcTan[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcTan[c+d*Tanh[a+b*x]]/(f*(m+1)) + 
  I*b*(I-c-d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*a+2*b*x)/(I-c+d+(I-c-d)*E^(2*a+2*b*x)),x] - 
  I*b*(I+c+d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*a+2*b*x)/(I+c-d+(I+c+d)*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveIntegerQ[m] && NeQ[(c-d)^2+1]


Int[(e_.+f_.*x_)^m_.*ArcCot[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcCot[c+d*Tanh[a+b*x]]/(f*(m+1)) - 
  I*b*(I-c-d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*a+2*b*x)/(I-c+d+(I-c-d)*E^(2*a+2*b*x)),x] + 
  I*b*(I+c+d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*a+2*b*x)/(I+c-d+(I+c+d)*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveIntegerQ[m] && NeQ[(c-d)^2+1]


Int[(e_.+f_.*x_)^m_.*ArcTan[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcTan[c+d*Coth[a+b*x]]/(f*(m+1)) - 
  I*b*(I-c-d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*a+2*b*x)/(I-c+d-(I-c-d)*E^(2*a+2*b*x)),x] + 
  I*b*(I+c+d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*a+2*b*x)/(I+c-d-(I+c+d)*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveIntegerQ[m] && NeQ[(c-d)^2+1]


Int[(e_.+f_.*x_)^m_.*ArcCot[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
  (e+f*x)^(m+1)*ArcCot[c+d*Coth[a+b*x]]/(f*(m+1)) + 
  I*b*(I-c-d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*a+2*b*x)/(I-c+d-(I-c-d)*E^(2*a+2*b*x)),x] - 
  I*b*(I+c+d)/(f*(m+1))*Int[(e+f*x)^(m+1)*E^(2*a+2*b*x)/(I+c-d-(I+c+d)*E^(2*a+2*b*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveIntegerQ[m] && NeQ[(c-d)^2+1]


Int[ArcTan[u_],x_Symbol] :=
  x*ArcTan[u] -
  Int[SimplifyIntegrand[x*D[u,x]/(1+u^2),x],x] /;
InverseFunctionFreeQ[u,x]


Int[ArcCot[u_],x_Symbol] :=
  x*ArcCot[u] +
  Int[SimplifyIntegrand[x*D[u,x]/(1+u^2),x],x] /;
InverseFunctionFreeQ[u,x]


Int[(c_.+d_.*x_)^m_.*(a_.+b_.*ArcTan[u_]),x_Symbol] :=
  (c+d*x)^(m+1)*(a+b*ArcTan[u])/(d*(m+1)) -
  b/(d*(m+1))*Int[SimplifyIntegrand[(c+d*x)^(m+1)*D[u,x]/(1+u^2),x],x] /;
FreeQ[{a,b,c,d,m},x] && NeQ[m+1] && InverseFunctionFreeQ[u,x] && Not[FunctionOfQ[(c+d*x)^(m+1),u,x]] && FalseQ[PowerVariableExpn[u,m+1,x]]


Int[(c_.+d_.*x_)^m_.*(a_.+b_.*ArcCot[u_]),x_Symbol] :=
  (c+d*x)^(m+1)*(a+b*ArcCot[u])/(d*(m+1)) +
  b/(d*(m+1))*Int[SimplifyIntegrand[(c+d*x)^(m+1)*D[u,x]/(1+u^2),x],x] /;
FreeQ[{a,b,c,d,m},x] && NeQ[m+1] && InverseFunctionFreeQ[u,x] && Not[FunctionOfQ[(c+d*x)^(m+1),u,x]] && FalseQ[PowerVariableExpn[u,m+1,x]]


Int[v_*(a_.+b_.*ArcTan[u_]),x_Symbol] :=
  With[{w=IntHide[v,x]},  
  Dist[(a+b*ArcTan[u]),w,x] - b*Int[SimplifyIntegrand[w*D[u,x]/(1+u^2),x],x] /;
 InverseFunctionFreeQ[w,x]] /;
FreeQ[{a,b},x] && InverseFunctionFreeQ[u,x] && Not[MatchQ[v, (c_.+d_.*x)^m_. /; FreeQ[{c,d,m},x]]] && FalseQ[FunctionOfLinear[v*(a+b*ArcTan[u]),x]]


Int[v_*(a_.+b_.*ArcCot[u_]),x_Symbol] :=
  With[{w=IntHide[v,x]},  
  Dist[(a+b*ArcCot[u]),w,x] + b*Int[SimplifyIntegrand[w*D[u,x]/(1+u^2),x],x] /;
 InverseFunctionFreeQ[w,x]] /;
FreeQ[{a,b},x] && InverseFunctionFreeQ[u,x] && Not[MatchQ[v, (c_.+d_.*x)^m_. /; FreeQ[{c,d,m},x]]] && FalseQ[FunctionOfLinear[v*(a+b*ArcCot[u]),x]]


Int[ArcTan[v_]*Log[w_]/(a_.+b_.*x_),x_Symbol] :=
  I/2*Int[Log[1-I*v]*Log[w]/(a+b*x),x] - I/2*Int[Log[1+I*v]*Log[w]/(a+b*x),x] /;
FreeQ[{a,b},x] && LinearQ[v,x] && LinearQ[w,x] && EqQ[Simplify[D[v/(a+b*x),x]]] && EqQ[Simplify[D[w/(a+b*x),x]]]


Int[ArcTan[v_]*Log[w_],x_Symbol] :=
  x*ArcTan[v]*Log[w] - 
  Int[SimplifyIntegrand[x*Log[w]*D[v,x]/(1+v^2),x],x] - 
  Int[SimplifyIntegrand[x*ArcTan[v]*D[w,x]/w,x],x] /;
InverseFunctionFreeQ[v,x] && InverseFunctionFreeQ[w,x]


Int[ArcCot[v_]*Log[w_],x_Symbol] :=
  x*ArcCot[v]*Log[w] + 
  Int[SimplifyIntegrand[x*Log[w]*D[v,x]/(1+v^2),x],x] - 
  Int[SimplifyIntegrand[x*ArcCot[v]*D[w,x]/w,x],x] /;
InverseFunctionFreeQ[v,x] && InverseFunctionFreeQ[w,x]


Int[u_*ArcTan[v_]*Log[w_],x_Symbol] :=
  With[{z=IntHide[u,x]},  
  Dist[ArcTan[v]*Log[w],z,x] - 
  Int[SimplifyIntegrand[z*Log[w]*D[v,x]/(1+v^2),x],x] - 
  Int[SimplifyIntegrand[z*ArcTan[v]*D[w,x]/w,x],x] /;
 InverseFunctionFreeQ[z,x]] /;
InverseFunctionFreeQ[v,x] && InverseFunctionFreeQ[w,x]


Int[u_*ArcCot[v_]*Log[w_],x_Symbol] :=
  With[{z=IntHide[u,x]},  
  Dist[ArcCot[v]*Log[w],z,x] + 
  Int[SimplifyIntegrand[z*Log[w]*D[v,x]/(1+v^2),x],x] - 
  Int[SimplifyIntegrand[z*ArcCot[v]*D[w,x]/w,x],x] /;
 InverseFunctionFreeQ[z,x]] /;
InverseFunctionFreeQ[v,x] && InverseFunctionFreeQ[w,x]





(* ::Subsection::Closed:: *)
(*5.3/1 Miscellaneous inverse secant*)


Int[ArcSec[c_.*x_],x_Symbol] :=
  x*ArcSec[c*x] - 1/c*Int[1/(x*Sqrt[1-1/(c^2*x^2)]),x] /;
FreeQ[c,x]


Int[ArcCsc[c_.*x_],x_Symbol] :=
  x*ArcCsc[c*x] + 1/c*Int[1/(x*Sqrt[1-1/(c^2*x^2)]),x] /;
FreeQ[c,x]


Int[(a_.+b_.*ArcSec[c_.*x_])^n_,x_Symbol] :=
  1/c*Subst[Int[(a+b*x)^n*Sec[x]*Tan[x],x],x,ArcSec[c*x]] /;
FreeQ[{a,b,c,n},x]


Int[(a_.+b_.*ArcCsc[c_.*x_])^n_,x_Symbol] :=
  -1/c*Subst[Int[(a+b*x)^n*Csc[x]*Cot[x],x],x,ArcCsc[c*x]] /;
FreeQ[{a,b,c,n},x]


Int[(a_.+b_.*ArcSec[c_.*x_])/x_,x_Symbol] :=
  -Subst[Int[(a+b*ArcCos[x/c])/x,x],x,1/x] /;
FreeQ[{a,b,c},x]


Int[(a_.+b_.*ArcCsc[c_.*x_])/x_,x_Symbol] :=
  -Subst[Int[(a+b*ArcSin[x/c])/x,x],x,1/x] /;
FreeQ[{a,b,c},x]


Int[x_^m_.*(a_.+b_.*ArcSec[c_.*x_]),x_Symbol] :=
  x^(m+1)*(a+b*ArcSec[c*x])/(m+1) - 
  b/(c*(m+1))*Int[x^(m-1)/Sqrt[1-1/(c^2*x^2)],x] /;
FreeQ[{a,b,c,m},x] && NeQ[m+1]


Int[x_^m_.*(a_.+b_.*ArcCsc[c_.*x_]),x_Symbol] :=
  x^(m+1)*(a+b*ArcCsc[c*x])/(m+1) +
  b/(c*(m+1))*Int[x^(m-1)/Sqrt[1-1/(c^2*x^2)],x] /;
FreeQ[{a,b,c,m},x] && NeQ[m+1]


Int[x_^m_.*(a_.+b_.*ArcSec[c_.*x_])^n_,x_Symbol] :=
  1/c^(m+1)*Subst[Int[(a+b*x)^n*Sec[x]^(m+1)*Tan[x],x],x,ArcSec[c*x]] /;
FreeQ[{a,b,c,n},x] && IntegerQ[m]


Int[x_^m_.*(a_.+b_.*ArcCsc[c_.*x_])^n_,x_Symbol] :=
  -1/c^(m+1)*Subst[Int[(a+b*x)^n*Csc[x]^(m+1)*Cot[x],x],x,ArcCsc[c*x]] /;
FreeQ[{a,b,c,n},x] && IntegerQ[m]


Int[x_^m_.*(a_.+b_.*ArcSec[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][x^m*(a+b*ArcSec[c*x])^n,x] /;
FreeQ[{a,b,c,m,n},x]


Int[x_^m_.*(a_.+b_.*ArcCsc[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][x^m*(a+b*ArcCsc[c*x])^n,x] /;
FreeQ[{a,b,c,m,n},x]


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSec[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(d+e*x^2)^p,x]},  
  Dist[(a+b*ArcSec[c*x]),u,x] - b*c*x/Sqrt[c^2*x^2]*Int[SimplifyIntegrand[u/(x*Sqrt[c^2*x^2-1]),x],x]] /;
FreeQ[{a,b,c,d,e},x] && (PositiveIntegerQ[p] || NegativeIntegerQ[p+1/2])


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCsc[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[(d+e*x^2)^p,x]},  
  Dist[(a+b*ArcCsc[c*x]),u,x] + b*c*x/Sqrt[c^2*x^2]*Int[SimplifyIntegrand[u/(x*Sqrt[c^2*x^2-1]),x],x]] /;
FreeQ[{a,b,c,d,e},x] && (PositiveIntegerQ[p] || NegativeIntegerQ[p+1/2])


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSec[c_.*x_])^n_.,x_Symbol] :=
  -Subst[Int[(e+d*x^2)^p*(a+b*ArcCos[x/c])^n/x^(2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && IntegerQ[p]


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCsc[c_.*x_])^n_.,x_Symbol] :=
  -Subst[Int[(e+d*x^2)^p*(a+b*ArcSin[x/c])^n/x^(2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && IntegerQ[p]


Int[(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcSec[c_.*x_])^n_.,x_Symbol] :=
  -Sqrt[x^2]/x*Subst[Int[(e+d*x^2)^p*(a+b*ArcCos[x/c])^n/x^(2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e] && IntegerQ[p+1/2] && PositiveQ[e] && Negative[d]


Int[(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcCsc[c_.*x_])^n_.,x_Symbol] :=
  -Sqrt[x^2]/x*Subst[Int[(e+d*x^2)^p*(a+b*ArcSin[x/c])^n/x^(2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e] && IntegerQ[p+1/2] && PositiveQ[e] && Negative[d]


Int[(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcSec[c_.*x_])^n_.,x_Symbol] :=
  -Sqrt[d+e*x^2]/(x*Sqrt[e+d/x^2])*Subst[Int[(e+d*x^2)^p*(a+b*ArcCos[x/c])^n/x^(2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e] && IntegerQ[p+1/2] && Not[PositiveQ[e] && Negative[d]]


Int[(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcCsc[c_.*x_])^n_.,x_Symbol] :=
  -Sqrt[d+e*x^2]/(x*Sqrt[e+d/x^2])*Subst[Int[(e+d*x^2)^p*(a+b*ArcSin[x/c])^n/x^(2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e] && IntegerQ[p+1/2] && Not[PositiveQ[e] && Negative[d]]


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSec[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(d+e*x^2)^p*(a+b*ArcSec[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n,p},x]


Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCsc[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(d+e*x^2)^p*(a+b*ArcCsc[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,n,p},x]


Int[x_*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSec[c_.*x_]),x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcSec[c*x])/(2*e*(p+1)) - 
  b*c*x/(2*e*(p+1)*Sqrt[c^2*x^2])*Int[(d+e*x^2)^(p+1)/(x*Sqrt[c^2*x^2-1]),x] /;
FreeQ[{a,b,c,d,e,p},x] && NeQ[p+1]


Int[x_*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCsc[c_.*x_]),x_Symbol] :=
  (d+e*x^2)^(p+1)*(a+b*ArcCsc[c*x])/(2*e*(p+1)) + 
  b*c*x/(2*e*(p+1)*Sqrt[c^2*x^2])*Int[(d+e*x^2)^(p+1)/(x*Sqrt[c^2*x^2-1]),x] /;
FreeQ[{a,b,c,d,e,p},x] && NeQ[p+1]


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSec[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[x^m*(d+e*x^2)^p,x]},  
  Dist[(a+b*ArcSec[c*x]),u,x] - b*c*x/Sqrt[c^2*x^2]*Int[SimplifyIntegrand[u/(x*Sqrt[c^2*x^2-1]),x],x]] /;
FreeQ[{a,b,c,d,e,m,p},x] && (
  PositiveIntegerQ[p] && Not[NegativeIntegerQ[(m-1)/2] && m+2*p+3>0] || 
  PositiveIntegerQ[(m+1)/2] && Not[NegativeIntegerQ[p] && m+2*p+3>0] || 
  NegativeIntegerQ[(m+2*p+1)/2] && Not[NegativeIntegerQ[(m-1)/2]] )


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCsc[c_.*x_]),x_Symbol] :=
  With[{u=IntHide[x^m*(d+e*x^2)^p,x]},  
  Dist[(a+b*ArcCsc[c*x]),u,x] + b*c*x/Sqrt[c^2*x^2]*Int[SimplifyIntegrand[u/(x*Sqrt[c^2*x^2-1]),x],x]] /;
FreeQ[{a,b,c,d,e,m,p},x] && (
  PositiveIntegerQ[p] && Not[NegativeIntegerQ[(m-1)/2] && m+2*p+3>0] || 
  PositiveIntegerQ[(m+1)/2] && Not[NegativeIntegerQ[p] && m+2*p+3>0] || 
  NegativeIntegerQ[(m+2*p+1)/2] && Not[NegativeIntegerQ[(m-1)/2]] )


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSec[c_.*x_])^n_.,x_Symbol] :=
  -Subst[Int[(e+d*x^2)^p*(a+b*ArcCos[x/c])^n/x^(m+2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && IntegersQ[m,p]


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCsc[c_.*x_])^n_.,x_Symbol] :=
  -Subst[Int[(e+d*x^2)^p*(a+b*ArcSin[x/c])^n/x^(m+2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && IntegersQ[m,p]


Int[x_^m_.*(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcSec[c_.*x_])^n_.,x_Symbol] :=
  -Sqrt[x^2]/x*Subst[Int[(e+d*x^2)^p*(a+b*ArcCos[x/c])^n/x^(m+2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e] && IntegerQ[m] && IntegerQ[p+1/2] && PositiveQ[e] && Negative[d]


Int[x_^m_.*(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcCsc[c_.*x_])^n_.,x_Symbol] :=
  -Sqrt[x^2]/x*Subst[Int[(e+d*x^2)^p*(a+b*ArcSin[x/c])^n/x^(m+2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e] && IntegerQ[m] && IntegerQ[p+1/2] && PositiveQ[e] && Negative[d]


Int[x_^m_.*(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcSec[c_.*x_])^n_.,x_Symbol] :=
  -Sqrt[d+e*x^2]/(x*Sqrt[e+d/x^2])*Subst[Int[(e+d*x^2)^p*(a+b*ArcCos[x/c])^n/x^(m+2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e] && IntegerQ[m] && IntegerQ[p+1/2] && Not[PositiveQ[e] && Negative[d]]


Int[x_^m_.*(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcCsc[c_.*x_])^n_.,x_Symbol] :=
  -Sqrt[d+e*x^2]/(x*Sqrt[e+d/x^2])*Subst[Int[(e+d*x^2)^p*(a+b*ArcSin[x/c])^n/x^(m+2*(p+1)),x],x,1/x] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e] && IntegerQ[m] && IntegerQ[p+1/2] && Not[PositiveQ[e] && Negative[d]]


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSec[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][x^m*(d+e*x^2)^p*(a+b*ArcSec[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x]


Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCsc[c_.*x_])^n_.,x_Symbol] :=
  Defer[Int][x^m*(d+e*x^2)^p*(a+b*ArcCsc[c*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x]


Int[ArcSec[a_+b_.*x_],x_Symbol] :=
  (a+b*x)*ArcSec[a+b*x]/b - 
  Int[1/((a+b*x)*Sqrt[1-1/(a+b*x)^2]),x] /;
FreeQ[{a,b},x]


Int[ArcCsc[a_+b_.*x_],x_Symbol] :=
  (a+b*x)*ArcCsc[a+b*x]/b + 
  Int[1/((a+b*x)*Sqrt[1-1/(a+b*x)^2]),x] /;
FreeQ[{a,b},x]


Int[ArcSec[a_+b_.*x_]^n_,x_Symbol] :=
  1/b*Subst[Int[x^n*Sec[x]*Tan[x],x],x,ArcSec[a+b*x]] /;
FreeQ[{a,b,n},x]


Int[ArcCsc[a_+b_.*x_]^n_,x_Symbol] :=
  -1/b*Subst[Int[x^n*Csc[x]*Cot[x],x],x,ArcCsc[a+b*x]] /;
FreeQ[{a,b,n},x]


Int[ArcSec[a_+b_.*x_]/x_,x_Symbol] :=
  ArcSec[a+b*x]*Log[1-(1-Sqrt[1-a^2])*E^(I*ArcSec[a+b*x])/a] + 
  ArcSec[a+b*x]*Log[1-(1+Sqrt[1-a^2])*E^(I*ArcSec[a+b*x])/a] - 
  ArcSec[a+b*x]*Log[1+E^(2*I*ArcSec[a+b*x])] - 
  I*PolyLog[2,(1-Sqrt[1-a^2])*E^(I*ArcSec[a+b*x])/a] - 
  I*PolyLog[2,(1+Sqrt[1-a^2])*E^(I*ArcSec[a+b*x])/a] + 
  1/2*I*PolyLog[2,-E^(2*I*ArcSec[a+b*x])] /;
FreeQ[{a,b},x]


Int[ArcCsc[a_+b_.*x_]/x_,x_Symbol] :=
  I*ArcCsc[a+b*x]^2 + 
  ArcCsc[a+b*x]*Log[1-I*(1-Sqrt[1-a^2])/(E^(I*ArcCsc[a+b*x])*a)] + 
  ArcCsc[a+b*x]*Log[1-I*(1+Sqrt[1-a^2])/(E^(I*ArcCsc[a+b*x])*a)] - 
  ArcCsc[a+b*x]*Log[1-E^(2*I*ArcCsc[a+b*x])] + 
  I*PolyLog[2,I*(1-Sqrt[1-a^2])/(E^(I*ArcCsc[a+b*x])*a)] + 
  I*PolyLog[2,I*(1+Sqrt[1-a^2])/(E^(I*ArcCsc[a+b*x])*a)] + 
  1/2*I*PolyLog[2,E^(2*I*ArcCsc[a+b*x])] /;
FreeQ[{a,b},x]


Int[x_^m_.*ArcSec[a_+b_.*x_],x_Symbol] :=
  -((-a)^(m+1)-b^(m+1)*x^(m+1))*ArcSec[a+b*x]/(b^(m+1)*(m+1)) - 
  1/(b^(m+1)*(m+1))*Subst[Int[(((-a)*x)^(m+1)-(1-a*x)^(m+1))/(x^(m+1)*Sqrt[1-x^2]),x],x,1/(a+b*x)] /;
FreeQ[{a,b,m},x] && IntegerQ[m] && NeQ[m+1]


Int[x_^m_.*ArcCsc[a_+b_.*x_],x_Symbol] :=
  -((-a)^(m+1)-b^(m+1)*x^(m+1))*ArcCsc[a+b*x]/(b^(m+1)*(m+1)) + 
  1/(b^(m+1)*(m+1))*Subst[Int[(((-a)*x)^(m+1)-(1-a*x)^(m+1))/(x^(m+1)*Sqrt[1-x^2]),x],x,1/(a+b*x)] /;
FreeQ[{a,b,m},x] && IntegerQ[m] && NeQ[m+1]


Int[x_^m_.*ArcSec[a_+b_.*x_]^n_,x_Symbol] :=
  1/b^(m+1)*Subst[Int[x^n*(-a+Sec[x])^m*Sec[x]*Tan[x],x],x,ArcSec[a+b*x]] /;
FreeQ[{a,b,n},x] && PositiveIntegerQ[m]


Int[x_^m_.*ArcCsc[a_+b_.*x_]^n_,x_Symbol] :=
  -1/b^(m+1)*Subst[Int[x^n*(-a+Csc[x])^m*Csc[x]*Cot[x],x],x,ArcCsc[a+b*x]] /;
FreeQ[{a,b,n},x] && PositiveIntegerQ[m]


Int[u_.*ArcSec[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
  Int[u*ArcCos[a/c+b*x^n/c]^m,x] /;
FreeQ[{a,b,c,n,m},x]


Int[u_.*ArcCsc[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
  Int[u*ArcSin[a/c+b*x^n/c]^m,x] /;
FreeQ[{a,b,c,n,m},x]


Int[u_.*f_^(c_.*ArcSec[a_.+b_.*x_]^n_.),x_Symbol] :=
  1/b*Subst[Int[ReplaceAll[u,x->-a/b+Sec[x]/b]*f^(c*x^n)*Sec[x]*Tan[x],x],x,ArcSec[a+b*x]] /;
FreeQ[{a,b,c,f},x] && PositiveIntegerQ[n]


Int[u_.*f_^(c_.*ArcCsc[a_.+b_.*x_]^n_.),x_Symbol] :=
  -1/b*Subst[Int[ReplaceAll[u,x->-a/b+Csc[x]/b]*f^(c*x^n)*Csc[x]*Cot[x],x],x,ArcCsc[a+b*x]] /;
FreeQ[{a,b,c,f},x] && PositiveIntegerQ[n]


Int[ArcSec[u_],x_Symbol] :=
  x*ArcSec[u] -
  u/Sqrt[u^2]*Int[SimplifyIntegrand[x*D[u,x]/(u*Sqrt[u^2-1]),x],x] /;
InverseFunctionFreeQ[u,x] && Not[FunctionOfExponentialQ[u,x]]


Int[ArcCsc[u_],x_Symbol] :=
  x*ArcCsc[u] +
  u/Sqrt[u^2]*Int[SimplifyIntegrand[x*D[u,x]/(u*Sqrt[u^2-1]),x],x] /;
InverseFunctionFreeQ[u,x] && Not[FunctionOfExponentialQ[u,x]]


Int[(c_.+d_.*x_)^m_.*(a_.+b_.*ArcSec[u_]),x_Symbol] :=
  (c+d*x)^(m+1)*(a+b*ArcSec[u])/(d*(m+1)) -
  b*u/(d*(m+1)*Sqrt[u^2])*Int[SimplifyIntegrand[(c+d*x)^(m+1)*D[u,x]/(u*Sqrt[u^2-1]),x],x] /;
FreeQ[{a,b,c,d,m},x] && NeQ[m+1] && InverseFunctionFreeQ[u,x] && Not[FunctionOfQ[(c+d*x)^(m+1),u,x]] && Not[FunctionOfExponentialQ[u,x]]


Int[(c_.+d_.*x_)^m_.*(a_.+b_.*ArcCsc[u_]),x_Symbol] :=
  (c+d*x)^(m+1)*(a+b*ArcCsc[u])/(d*(m+1)) +
  b*u/(d*(m+1)*Sqrt[u^2])*Int[SimplifyIntegrand[(c+d*x)^(m+1)*D[u,x]/(u*Sqrt[u^2-1]),x],x] /;
FreeQ[{a,b,c,d,m},x] && NeQ[m+1] && InverseFunctionFreeQ[u,x] && Not[FunctionOfQ[(c+d*x)^(m+1),u,x]] && Not[FunctionOfExponentialQ[u,x]]


Int[v_*(a_.+b_.*ArcSec[u_]),x_Symbol] :=
  With[{w=IntHide[v,x]},  
  Dist[(a+b*ArcSec[u]),w,x] - b*u/Sqrt[u^2]*Int[SimplifyIntegrand[w*D[u,x]/(u*Sqrt[u^2-1]),x],x] /;
 InverseFunctionFreeQ[w,x]] /;
FreeQ[{a,b},x] && InverseFunctionFreeQ[u,x] && Not[MatchQ[v, (c_.+d_.*x)^m_. /; FreeQ[{c,d,m},x]]]


Int[v_*(a_.+b_.*ArcCsc[u_]),x_Symbol] :=
  With[{w=IntHide[v,x]},  
  Dist[(a+b*ArcCsc[u]),w,x] + b*u/Sqrt[u^2]*Int[SimplifyIntegrand[w*D[u,x]/(u*Sqrt[u^2-1]),x],x] /;
 InverseFunctionFreeQ[w,x]] /;
FreeQ[{a,b},x] && InverseFunctionFreeQ[u,x] && Not[MatchQ[v, (c_.+d_.*x)^m_. /; FreeQ[{c,d,m},x]]]



