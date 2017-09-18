(* ::Package:: *)

(* ::Section:: *)
(*Miscellaneous Trig Function Rules*)


(* ::Subsection::Closed:: *)
(*4.1 Sine normalization rules*)


Int[u_*(c_.*tan[a_.+b_.*x_])^m_.*(d_.*sin[a_.+b_.*x_])^n_.,x_Symbol] :=
  (c*Tan[a+b*x])^m*(d*Cos[a+b*x])^m/(d*Sin[a+b*x])^m*Int[ActivateTrig[u]*(d*Sin[a+b*x])^(m+n)/(d*Cos[a+b*x])^m,x] /;
FreeQ[{a,b,c,d,m,n},x] && KnownSineIntegrandQ[u,x] && Not[IntegerQ[m]]


Int[u_*(c_.*tan[a_.+b_.*x_])^m_.*(d_.*cos[a_.+b_.*x_])^n_.,x_Symbol] :=
  (c*Tan[a+b*x])^m*(d*Cos[a+b*x])^m/(d*Sin[a+b*x])^m*Int[ActivateTrig[u]*(d*Sin[a+b*x])^m/(d*Cos[a+b*x])^(m-n),x] /;
FreeQ[{a,b,c,d,m,n},x] && KnownSineIntegrandQ[u,x] && Not[IntegerQ[m]]


Int[u_*(c_.*cot[a_.+b_.*x_])^m_.*(d_.*sin[a_.+b_.*x_])^n_.,x_Symbol] :=
  (c*Cot[a+b*x])^m*(d*Sin[a+b*x])^m/(d*Cos[a+b*x])^m*Int[ActivateTrig[u]*(d*Cos[a+b*x])^m/(d*Sin[a+b*x])^(m-n),x] /;
FreeQ[{a,b,c,d,m,n},x] && KnownSineIntegrandQ[u,x] && Not[IntegerQ[m]]


Int[u_*(c_.*cot[a_.+b_.*x_])^m_.*(d_.*cos[a_.+b_.*x_])^n_.,x_Symbol] :=
  (c*Cot[a+b*x])^m*(d*Sin[a+b*x])^m/(d*Cos[a+b*x])^m*Int[ActivateTrig[u]*(d*Cos[a+b*x])^(m+n)/(d*Sin[a+b*x])^m,x] /;
FreeQ[{a,b,c,d,m,n},x] && KnownSineIntegrandQ[u,x] && Not[IntegerQ[m]]


Int[u_*(c_.*sec[a_.+b_.*x_])^m_.*(d_.*cos[a_.+b_.*x_])^n_.,x_Symbol] :=
  (c*Sec[a+b*x])^m*(d*Cos[a+b*x])^m*Int[ActivateTrig[u]*(d*Cos[a+b*x])^(n-m),x] /;
FreeQ[{a,b,c,d,m,n},x] && KnownSineIntegrandQ[u,x]


Int[u_*(c_.*sec[a_.+b_.*x_])^m_.*(d_.*cos[a_.+b_.*x_])^n_.,x_Symbol] :=
  (c*Csc[a+b*x])^m*(d*Sin[a+b*x])^m*Int[ActivateTrig[u]*(d*Sin[a+b*x])^(n-m),x] /;
FreeQ[{a,b,c,d,m,n},x] && KnownSineIntegrandQ[u,x]


Int[u_*(c_.*tan[a_.+b_.*x_])^m_.,x_Symbol] :=
  (c*Tan[a+b*x])^m*(c*Cos[a+b*x])^m/(c*Sin[a+b*x])^m*Int[ActivateTrig[u]*(c*Sin[a+b*x])^m/(c*Cos[a+b*x])^m,x] /;
FreeQ[{a,b,c,m},x] && Not[IntegerQ[m]] && KnownSineIntegrandQ[u,x]


Int[u_*(c_.*cot[a_.+b_.*x_])^m_.,x_Symbol] :=
  (c*Cot[a+b*x])^m*(c*Sin[a+b*x])^m/(c*Cos[a+b*x])^m*Int[ActivateTrig[u]*(c*Cos[a+b*x])^m/(c*Sin[a+b*x])^m,x] /;
FreeQ[{a,b,c,m},x] && Not[IntegerQ[m]] && KnownSineIntegrandQ[u,x]


Int[u_*(c_.*sec[a_.+b_.*x_])^m_.,x_Symbol] :=
  (c*Sec[a+b*x])^m*(c*Cos[a+b*x])^m*Int[ActivateTrig[u]/(c*Cos[a+b*x])^m,x] /;
FreeQ[{a,b,c,m},x] && Not[IntegerQ[m]] && KnownSineIntegrandQ[u,x]


Int[u_*(c_.*csc[a_.+b_.*x_])^m_.,x_Symbol] :=
  (c*Csc[a+b*x])^m*(c*Sin[a+b*x])^m*Int[ActivateTrig[u]/(c*Sin[a+b*x])^m,x] /;
FreeQ[{a,b,c,m},x] && Not[IntegerQ[m]] && KnownSineIntegrandQ[u,x]


Int[u_*(c_.*sin[a_.+b_.*x_])^n_.*(A_+B_.*csc[a_.+b_.*x_]),x_Symbol] :=
  c*Int[ActivateTrig[u]*(c*Sin[a+b*x])^(n-1)*(B+A*Sin[a+b*x]),x] /;
FreeQ[{a,b,c,A,B,n},x] && KnownSineIntegrandQ[u,x]


Int[u_*(c_.*cos[a_.+b_.*x_])^n_.*(A_+B_.*sec[a_.+b_.*x_]),x_Symbol] :=
  c*Int[ActivateTrig[u]*(c*Cos[a+b*x])^(n-1)*(B+A*Cos[a+b*x]),x] /;
FreeQ[{a,b,c,A,B,n},x] && KnownSineIntegrandQ[u,x]


Int[u_*(A_+B_.*csc[a_.+b_.*x_]),x_Symbol] :=
  Int[ActivateTrig[u]*(B+A*Sin[a+b*x])/Sin[a+b*x],x] /;
FreeQ[{a,b,A,B},x] && KnownSineIntegrandQ[u,x]


Int[u_*(A_+B_.*sec[a_.+b_.*x_]),x_Symbol] :=
  Int[ActivateTrig[u]*(B+A*Cos[a+b*x])/Cos[a+b*x],x] /;
FreeQ[{a,b,A,B},x] && KnownSineIntegrandQ[u,x]


Int[u_.*(c_.*sin[a_.+b_.*x_])^n_.*(A_.+B_.*csc[a_.+b_.*x_]+C_.*csc[a_.+b_.*x_]^2),x_Symbol] :=
  c^2*Int[ActivateTrig[u]*(c*Sin[a+b*x])^(n-2)*(C+B*Sin[a+b*x]+A*Sin[a+b*x]^2),x] /;
FreeQ[{a,b,c,A,B,C,n},x] && KnownSineIntegrandQ[u,x]


Int[u_.*(c_.*cos[a_.+b_.*x_])^n_.*(A_.+B_.*sec[a_.+b_.*x_]+C_.*sec[a_.+b_.*x_]^2),x_Symbol] :=
  c^2*Int[ActivateTrig[u]*(c*Cos[a+b*x])^(n-2)*(C+B*Cos[a+b*x]+A*Cos[a+b*x]^2),x] /;
FreeQ[{a,b,c,A,B,C,n},x] && KnownSineIntegrandQ[u,x]


Int[u_.*(c_.*sin[a_.+b_.*x_])^n_.*(A_+C_.*csc[a_.+b_.*x_]^2),x_Symbol] :=
  c^2*Int[ActivateTrig[u]*(c*Sin[a+b*x])^(n-2)*(C+A*Sin[a+b*x]^2),x] /;
FreeQ[{a,b,c,A,C,n},x] && KnownSineIntegrandQ[u,x]


Int[u_.*(c_.*cos[a_.+b_.*x_])^n_.*(A_+C_.*sec[a_.+b_.*x_]^2),x_Symbol] :=
  c^2*Int[ActivateTrig[u]*(c*Cos[a+b*x])^(n-2)*(C+A*Cos[a+b*x]^2),x] /;
FreeQ[{a,b,c,A,C,n},x] && KnownSineIntegrandQ[u,x]


Int[u_*(A_.+B_.*csc[a_.+b_.*x_]+C_.*csc[a_.+b_.*x_]^2),x_Symbol] :=
  Int[ActivateTrig[u]*(C+B*Sin[a+b*x]+A*Sin[a+b*x]^2)/Sin[a+b*x]^2,x] /;
FreeQ[{a,b,A,B,C},x] && KnownSineIntegrandQ[u,x]


Int[u_*(A_.+B_.*sec[a_.+b_.*x_]+C_.*sec[a_.+b_.*x_]^2),x_Symbol] :=
  Int[ActivateTrig[u]*(C+B*Cos[a+b*x]+A*Cos[a+b*x]^2)/Cos[a+b*x]^2,x] /;
FreeQ[{a,b,A,B,C},x] && KnownSineIntegrandQ[u,x]


Int[u_*(A_+C_.*csc[a_.+b_.*x_]^2),x_Symbol] :=
  Int[ActivateTrig[u]*(C+A*Sin[a+b*x]^2)/Sin[a+b*x]^2,x] /;
FreeQ[{a,b,A,C},x] && KnownSineIntegrandQ[u,x]


Int[u_*(A_+C_.*sec[a_.+b_.*x_]^2),x_Symbol] :=
  Int[ActivateTrig[u]*(C+A*Cos[a+b*x]^2)/Cos[a+b*x]^2,x] /;
FreeQ[{a,b,A,C},x] && KnownSineIntegrandQ[u,x]


Int[u_*(A_.+B_.*sin[a_.+b_.*x_]+C_.*csc[a_.+b_.*x_]),x_Symbol] :=
  Int[ActivateTrig[u]*(C+A*Sin[a+b*x]+B*Sin[a+b*x]^2)/Sin[a+b*x],x] /;
FreeQ[{a,b,A,B,C},x]


Int[u_*(A_.+B_.*cos[a_.+b_.*x_]+C_.*sec[a_.+b_.*x_]),x_Symbol] :=
  Int[ActivateTrig[u]*(C+A*Cos[a+b*x]+B*Cos[a+b*x]^2)/Cos[a+b*x],x] /;
FreeQ[{a,b,A,B,C},x]


Int[u_*(A_.*sin[a_.+b_.*x_]^n_.+B_.*sin[a_.+b_.*x_]^n1_+C_.*sin[a_.+b_.*x_]^n2_),x_Symbol] :=
  Int[ActivateTrig[u]*Sin[a+b*x]^n*(A+B*Sin[a+b*x]+C*Sin[a+b*x]^2),x] /;
FreeQ[{a,b,A,B,C,n},x] && EqQ[n1-n-1] && EqQ[n2-n-2]


Int[u_*(A_.*cos[a_.+b_.*x_]^n_.+B_.*cos[a_.+b_.*x_]^n1_+C_.*cos[a_.+b_.*x_]^n2_),x_Symbol] :=
  Int[ActivateTrig[u]*Cos[a+b*x]^n*(A+B*Cos[a+b*x]+C*Cos[a+b*x]^2),x] /;
FreeQ[{a,b,A,B,C,n},x] && EqQ[n1-n-1] && EqQ[n2-n-2]





(* ::Subsection::Closed:: *)
(*4.2 Tangent normalization rules*)


Int[u_*(c_.*cot[a_.+b_.*x_])^m_.*(d_.*tan[a_.+b_.*x_])^n_.,x_Symbol] :=
  (c*Cot[a+b*x])^m*(d*Tan[a+b*x])^m*Int[ActivateTrig[u]*(d*Tan[a+b*x])^(n-m),x] /;
FreeQ[{a,b,c,d,m,n},x] && KnownTangentIntegrandQ[u,x]


Int[u_*(c_.*tan[a_.+b_.*x_])^m_.*(d_.*cos[a_.+b_.*x_])^n_.,x_Symbol] :=
  (c*Tan[a+b*x])^m*(d*Cos[a+b*x])^m/(d*Sin[a+b*x])^m*Int[ActivateTrig[u]*(d*Sin[a+b*x])^m/(d*Cos[a+b*x])^(m-n),x] /;
FreeQ[{a,b,c,d,m,n},x] && KnownCotangentIntegrandQ[u,x]


Int[u_*(c_.*cot[a_.+b_.*x_])^m_.,x_Symbol] :=
  (c*Cot[a+b*x])^m*(c*Tan[a+b*x])^m*Int[ActivateTrig[u]/(c*Tan[a+b*x])^m,x] /;
FreeQ[{a,b,c,m},x] && Not[IntegerQ[m]] && KnownTangentIntegrandQ[u,x]


Int[u_*(c_.*tan[a_.+b_.*x_])^m_.,x_Symbol] :=
  (c*Cot[a+b*x])^m*(c*Tan[a+b*x])^m*Int[ActivateTrig[u]/(c*Cot[a+b*x])^m,x] /;
FreeQ[{a,b,c,m},x] && Not[IntegerQ[m]] && KnownCotangentIntegrandQ[u,x]


Int[u_*(c_.*tan[a_.+b_.*x_])^n_.*(A_+B_.*cot[a_.+b_.*x_]),x_Symbol] :=
  c*Int[ActivateTrig[u]*(c*Tan[a+b*x])^(n-1)*(B+A*Tan[a+b*x]),x] /;
FreeQ[{a,b,c,A,B,n},x] && KnownTangentIntegrandQ[u,x]


Int[u_*(c_.*cot[a_.+b_.*x_])^n_.*(A_+B_.*tan[a_.+b_.*x_]),x_Symbol] :=
  c*Int[ActivateTrig[u]*(c*Cot[a+b*x])^(n-1)*(B+A*Cot[a+b*x]),x] /;
FreeQ[{a,b,c,A,B,n},x] && KnownCotangentIntegrandQ[u,x]


Int[u_*(A_+B_.*cot[a_.+b_.*x_]),x_Symbol] :=
  Int[ActivateTrig[u]*(B+A*Tan[a+b*x])/Tan[a+b*x],x] /;
FreeQ[{a,b,A,B},x] && KnownTangentIntegrandQ[u,x]


Int[u_*(A_+B_.*tan[a_.+b_.*x_]),x_Symbol] :=
  Int[ActivateTrig[u]*(B+A*Cot[a+b*x])/Cot[a+b*x],x] /;
FreeQ[{a,b,A,B},x] && KnownCotangentIntegrandQ[u,x]


Int[u_.*(c_.*tan[a_.+b_.*x_])^n_.*(A_.+B_.*cot[a_.+b_.*x_]+C_.*cot[a_.+b_.*x_]^2),x_Symbol] :=
  c^2*Int[ActivateTrig[u]*(c*Tan[a+b*x])^(n-2)*(C+B*Tan[a+b*x]+A*Tan[a+b*x]^2),x] /;
FreeQ[{a,b,c,A,B,C,n},x] && KnownTangentIntegrandQ[u,x]


Int[u_.*(c_.*cot[a_.+b_.*x_])^n_.*(A_.+B_.*tan[a_.+b_.*x_]+C_.*tan[a_.+b_.*x_]^2),x_Symbol] :=
  c^2*Int[ActivateTrig[u]*(c*Cot[a+b*x])^(n-2)*(C+B*Cot[a+b*x]+A*Cot[a+b*x]^2),x] /;
FreeQ[{a,b,c,A,B,C,n},x] && KnownCotangentIntegrandQ[u,x]


Int[u_.*(c_.*tan[a_.+b_.*x_])^n_.*(A_+C_.*cot[a_.+b_.*x_]^2),x_Symbol] :=
  c^2*Int[ActivateTrig[u]*(c*Tan[a+b*x])^(n-2)*(C+A*Tan[a+b*x]^2),x] /;
FreeQ[{a,b,c,A,C,n},x] && KnownTangentIntegrandQ[u,x]


Int[u_.*(c_.*cot[a_.+b_.*x_])^n_.*(A_+C_.*tan[a_.+b_.*x_]^2),x_Symbol] :=
  c^2*Int[ActivateTrig[u]*(c*Cot[a+b*x])^(n-2)*(C+A*Cot[a+b*x]^2),x] /;
FreeQ[{a,b,c,A,C,n},x] && KnownCotangentIntegrandQ[u,x]


Int[u_*(A_.+B_.*cot[a_.+b_.*x_]+C_.*cot[a_.+b_.*x_]^2),x_Symbol] :=
  Int[ActivateTrig[u]*(C+B*Tan[a+b*x]+A*Tan[a+b*x]^2)/Tan[a+b*x]^2,x] /;
FreeQ[{a,b,A,B,C},x] && KnownTangentIntegrandQ[u,x]


Int[u_*(A_.+B_.*tan[a_.+b_.*x_]+C_.*tan[a_.+b_.*x_]^2),x_Symbol] :=
  Int[ActivateTrig[u]*(C+B*Cot[a+b*x]+A*Cot[a+b*x]^2)/Cot[a+b*x]^2,x] /;
FreeQ[{a,b,A,B,C},x] && KnownCotangentIntegrandQ[u,x]


Int[u_*(A_+C_.*cot[a_.+b_.*x_]^2),x_Symbol] :=
  Int[ActivateTrig[u]*(C+A*Tan[a+b*x]^2)/Tan[a+b*x]^2,x] /;
FreeQ[{a,b,A,C},x] && KnownTangentIntegrandQ[u,x]


Int[u_*(A_+C_.*tan[a_.+b_.*x_]^2),x_Symbol] :=
  Int[ActivateTrig[u]*(C+A*Cot[a+b*x]^2)/Cot[a+b*x]^2,x] /;
FreeQ[{a,b,A,C},x] && KnownCotangentIntegrandQ[u,x]


Int[u_*(A_.+B_.*tan[a_.+b_.*x_]+C_.*cot[a_.+b_.*x_]),x_Symbol] :=
  Int[ActivateTrig[u]*(C+A*Tan[a+b*x]+B*Tan[a+b*x]^2)/Tan[a+b*x],x] /;
FreeQ[{a,b,A,B,C},x]


Int[u_*(A_.*tan[a_.+b_.*x_]^n_.+B_.*tan[a_.+b_.*x_]^n1_+C_.*tan[a_.+b_.*x_]^n2_),x_Symbol] :=
  Int[ActivateTrig[u]*Tan[a+b*x]^n*(A+B*Tan[a+b*x]+C*Tan[a+b*x]^2),x] /;
FreeQ[{a,b,A,B,C,n},x] && EqQ[n1-n-1] && EqQ[n2-n-2]


Int[u_*(A_.*cot[a_.+b_.*x_]^n_.+B_.*cot[a_.+b_.*x_]^n1_+C_.*cot[a_.+b_.*x_]^n2_),x_Symbol] :=
  Int[ActivateTrig[u]*Cot[a+b*x]^n*(A+B*Cot[a+b*x]+C*Cot[a+b*x]^2),x] /;
FreeQ[{a,b,A,B,C,n},x] && EqQ[n1-n-1] && EqQ[n2-n-2]





(* ::Subsection::Closed:: *)
(*4.3 Secant normalization rules*)
(**)


Int[u_*(c_.*sin[a_.+b_.*x_])^m_.*(d_.*csc[a_.+b_.*x_])^n_.,x_Symbol] :=
  (c*Sin[a+b*x])^m*(d*Csc[a+b*x])^m*Int[ActivateTrig[u]*(d*Csc[a+b*x])^(n-m),x] /;
FreeQ[{a,b,c,d,m,n},x] && KnownSecantIntegrandQ[u,x]


Int[u_*(c_.*cos[a_.+b_.*x_])^m_.*(d_.*sec[a_.+b_.*x_])^n_.,x_Symbol] :=
  (c*Cos[a+b*x])^m*(d*Sec[a+b*x])^m*Int[ActivateTrig[u]*(d*Sec[a+b*x])^(n-m),x] /;
FreeQ[{a,b,c,d,m,n},x] && KnownSecantIntegrandQ[u,x]


Int[u_*(c_.*tan[a_.+b_.*x_])^m_.*(d_.*sec[a_.+b_.*x_])^n_.,x_Symbol] :=
  (c*Tan[a+b*x])^m*(d*Csc[a+b*x])^m/(d*Sec[a+b*x])^m*Int[ActivateTrig[u]*(d*Sec[a+b*x])^(m+n)/(d*Csc[a+b*x])^m,x] /;
FreeQ[{a,b,c,d,m,n},x] && KnownSecantIntegrandQ[u,x] && Not[IntegerQ[m]]


Int[u_*(c_.*tan[a_.+b_.*x_])^m_.*(d_.*csc[a_.+b_.*x_])^n_.,x_Symbol] :=
  (c*Tan[a+b*x])^m*(d*Csc[a+b*x])^m/(d*Sec[a+b*x])^m*Int[ActivateTrig[u]*(d*Sec[a+b*x])^m/(d*Csc[a+b*x])^(m-n),x] /;
FreeQ[{a,b,c,d,m,n},x] && KnownSecantIntegrandQ[u,x] && Not[IntegerQ[m]]


Int[u_*(c_.*cot[a_.+b_.*x_])^m_.*(d_.*sec[a_.+b_.*x_])^n_.,x_Symbol] :=
  (c*Cot[a+b*x])^m*(d*Sec[a+b*x])^m/(d*Csc[a+b*x])^m*Int[ActivateTrig[u]*(d*Csc[a+b*x])^m/(d*Sec[a+b*x])^(m-n),x] /;
FreeQ[{a,b,c,d,m,n},x] && KnownSecantIntegrandQ[u,x] && Not[IntegerQ[m]]


Int[u_*(c_.*cot[a_.+b_.*x_])^m_.*(d_.*csc[a_.+b_.*x_])^n_.,x_Symbol] :=
  (c*Cot[a+b*x])^m*(d*Sec[a+b*x])^m/(d*Csc[a+b*x])^m*Int[ActivateTrig[u]*(d*Csc[a+b*x])^(m+n)/(d*Sec[a+b*x])^m,x] /;
FreeQ[{a,b,c,d,m,n},x] && KnownSecantIntegrandQ[u,x] && Not[IntegerQ[m]]


Int[u_*(c_.*sin[a_.+b_.*x_])^m_.,x_Symbol] :=
  (c*Csc[a+b*x])^m*(c*Sin[a+b*x])^m*Int[ActivateTrig[u]/(c*Csc[a+b*x])^m,x] /;
FreeQ[{a,b,c,m},x] && Not[IntegerQ[m]] && KnownSecantIntegrandQ[u,x]


Int[u_*(c_.*cos[a_.+b_.*x_])^m_.,x_Symbol] :=
  (c*Cos[a+b*x])^m*(c*Sec[a+b*x])^m*Int[ActivateTrig[u]/(c*Sec[a+b*x])^m,x] /;
FreeQ[{a,b,c,m},x] && Not[IntegerQ[m]] && KnownSecantIntegrandQ[u,x]


Int[u_*(c_.*tan[a_.+b_.*x_])^m_.,x_Symbol] :=
  (c*Tan[a+b*x])^m*(c*Csc[a+b*x])^m/(c*Sec[a+b*x])^m*Int[ActivateTrig[u]*(c*Sec[a+b*x])^m/(c*Csc[a+b*x])^m,x] /;
FreeQ[{a,b,c,m},x] && Not[IntegerQ[m]] && KnownSecantIntegrandQ[u,x]


Int[u_*(c_.*cot[a_.+b_.*x_])^m_.,x_Symbol] :=
  (c*Cot[a+b*x])^m*(c*Sec[a+b*x])^m/(c*Csc[a+b*x])^m*Int[ActivateTrig[u]*(c*Csc[a+b*x])^m/(c*Sec[a+b*x])^m,x] /;
FreeQ[{a,b,c,m},x] && Not[IntegerQ[m]] && KnownSecantIntegrandQ[u,x]


Int[u_*(c_.*sec[a_.+b_.*x_])^n_.*(A_+B_.*cos[a_.+b_.*x_]),x_Symbol] :=
  c*Int[ActivateTrig[u]*(c*Sec[a+b*x])^(n-1)*(B+A*Sec[a+b*x]),x] /;
FreeQ[{a,b,c,A,B,n},x] && KnownSecantIntegrandQ[u,x]


Int[u_*(c_.*csc[a_.+b_.*x_])^n_.*(A_+B_.*sin[a_.+b_.*x_]),x_Symbol] :=
  c*Int[ActivateTrig[u]*(c*Csc[a+b*x])^(n-1)*(B+A*Csc[a+b*x]),x] /;
FreeQ[{a,b,c,A,B,n},x] && KnownSecantIntegrandQ[u,x]


Int[u_*(A_+B_.*cos[a_.+b_.*x_]),x_Symbol] :=
  Int[ActivateTrig[u]*(B+A*Sec[a+b*x])/Sec[a+b*x],x] /;
FreeQ[{a,b,A,B},x] && KnownSecantIntegrandQ[u,x]


Int[u_*(A_+B_.*sin[a_.+b_.*x_]),x_Symbol] :=
  Int[ActivateTrig[u]*(B+A*Csc[a+b*x])/Csc[a+b*x],x] /;
FreeQ[{a,b,A,B},x] && KnownSecantIntegrandQ[u,x]


Int[u_.*(c_.*sec[a_.+b_.*x_])^n_.*(A_.+B_.*cos[a_.+b_.*x_]+C_.*cos[a_.+b_.*x_]^2),x_Symbol] :=
  c^2*Int[ActivateTrig[u]*(c*Sec[a+b*x])^(n-2)*(C+B*Sec[a+b*x]+A*Sec[a+b*x]^2),x] /;
FreeQ[{a,b,c,A,B,C,n},x] && KnownSecantIntegrandQ[u,x]


Int[u_.*(c_.*csc[a_.+b_.*x_])^n_.*(A_.+B_.*sin[a_.+b_.*x_]+C_.*sin[a_.+b_.*x_]^2),x_Symbol] :=
  c^2*Int[ActivateTrig[u]*(c*Csc[a+b*x])^(n-2)*(C+B*Csc[a+b*x]+A*Csc[a+b*x]^2),x] /;
FreeQ[{a,b,c,A,B,C,n},x] && KnownSecantIntegrandQ[u,x]


Int[u_.*(c_.*sec[a_.+b_.*x_])^n_.*(A_+C_.*cos[a_.+b_.*x_]^2),x_Symbol] :=
  c^2*Int[ActivateTrig[u]*(c*Sec[a+b*x])^(n-2)*(C+A*Sec[a+b*x]^2),x] /;
FreeQ[{a,b,c,A,C,n},x] && KnownSecantIntegrandQ[u,x]


Int[u_.*(c_.*csc[a_.+b_.*x_])^n_.*(A_+C_.*sin[a_.+b_.*x_]^2),x_Symbol] :=
  c^2*Int[ActivateTrig[u]*(c*Csc[a+b*x])^(n-2)*(C+A*Csc[a+b*x]^2),x] /;
FreeQ[{a,b,c,A,C,n},x] && KnownSecantIntegrandQ[u,x]


Int[u_*(A_.+B_.*cos[a_.+b_.*x_]+C_.*cos[a_.+b_.*x_]^2),x_Symbol] :=
  Int[ActivateTrig[u]*(C+B*Sec[a+b*x]+A*Sec[a+b*x]^2)/Sec[a+b*x]^2,x] /;
FreeQ[{a,b,A,B,C},x] && KnownSecantIntegrandQ[u,x]


Int[u_*(A_.+B_.*sin[a_.+b_.*x_]+C_.*sin[a_.+b_.*x_]^2),x_Symbol] :=
  Int[ActivateTrig[u]*(C+B*Csc[a+b*x]+A*Csc[a+b*x]^2)/Csc[a+b*x]^2,x] /;
FreeQ[{a,b,A,B,C},x] && KnownSecantIntegrandQ[u,x]


Int[u_*(A_+C_.*cos[a_.+b_.*x_]^2),x_Symbol] :=
  Int[ActivateTrig[u]*(C+A*Sec[a+b*x]^2)/Sec[a+b*x]^2,x] /;
FreeQ[{a,b,A,C},x] && KnownSecantIntegrandQ[u,x]


Int[u_*(A_+C_.*sin[a_.+b_.*x_]^2),x_Symbol] :=
  Int[ActivateTrig[u]*(C+A*Csc[a+b*x]^2)/Csc[a+b*x]^2,x] /;
FreeQ[{a,b,A,C},x] && KnownSecantIntegrandQ[u,x]


Int[u_*(A_.*sec[a_.+b_.*x_]^n_.+B_.*sec[a_.+b_.*x_]^n1_+C_.*sec[a_.+b_.*x_]^n2_),x_Symbol] :=
  Int[ActivateTrig[u]*Sec[a+b*x]^n*(A+B*Sec[a+b*x]+C*Sec[a+b*x]^2),x] /;
FreeQ[{a,b,A,B,C,n},x] && EqQ[n1-n-1] && EqQ[n2-n-2]


Int[u_*(A_.*csc[a_.+b_.*x_]^n_.+B_.*csc[a_.+b_.*x_]^n1_+C_.*csc[a_.+b_.*x_]^n2_),x_Symbol] :=
  Int[ActivateTrig[u]*Csc[a+b*x]^n*(A+B*Csc[a+b*x]+C*Csc[a+b*x]^2),x] /;
FreeQ[{a,b,A,B,C,n},x] && EqQ[n1-n-1] && EqQ[n2-n-2]





(* ::Subsection::Closed:: *)
(*4.4.1 (c trig)^m (d trig)^n*)


Int[sin[a_.+b_.*x_]*sin[c_.+d_.*x_],x_Symbol] :=
  Sin[a-c+(b-d)*x]/(2*(b-d)) - Sin[a+c+(b+d)*x]/(2*(b+d)) /;
FreeQ[{a,b,c,d},x] && NeQ[b^2-d^2]


Int[cos[a_.+b_.*x_]*cos[c_.+d_.*x_],x_Symbol] :=
  Sin[a-c+(b-d)*x]/(2*(b-d)) + Sin[a+c+(b+d)*x]/(2*(b+d)) /;
FreeQ[{a,b,c,d},x] && NeQ[b^2-d^2]


Int[sin[a_.+b_.*x_]*cos[c_.+d_.*x_],x_Symbol] :=
  -Cos[a-c+(b-d)*x]/(2*(b-d)) - Cos[a+c+(b+d)*x]/(2*(b+d)) /;
FreeQ[{a,b,c,d},x] && NeQ[b^2-d^2]


Int[cos[a_.+b_.*x_]^2*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  1/2*Int[(g*Sin[c+d*x])^p,x] + 
  1/2*Int[Cos[c+d*x]*(g*Sin[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,g},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && PositiveIntegerQ[p/2]


Int[sin[a_.+b_.*x_]^2*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  1/2*Int[(g*Sin[c+d*x])^p,x] - 
  1/2*Int[Cos[c+d*x]*(g*Sin[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,g},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && PositiveIntegerQ[p/2]


Int[(e_.*cos[a_.+b_.*x_])^m_.*sin[c_.+d_.*x_]^p_.,x_Symbol] :=
  2^p/e^p*Int[(e*Cos[a+b*x])^(m+p)*Sin[a+b*x]^p,x] /;
FreeQ[{a,b,c,d,e,m},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && IntegerQ[p]


Int[(f_.*sin[a_.+b_.*x_])^n_.*sin[c_.+d_.*x_]^p_.,x_Symbol] :=
  2^p/f^p*Int[Cos[a+b*x]^p*(f*Sin[a+b*x])^(n+p),x] /;
FreeQ[{a,b,c,d,f,n},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && IntegerQ[p]


Int[(e_.*cos[a_.+b_.*x_])^m_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  e^2*(e*Cos[a+b*x])^(m-2)*(g*Sin[c+d*x])^(p+1)/(2*b*g*(p+1)) /;
FreeQ[{a,b,c,d,e,g,m,p},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && Not[IntegerQ[p]] && EqQ[m+p-1]


Int[(e_.*sin[a_.+b_.*x_])^m_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  -e^2*(e*Sin[a+b*x])^(m-2)*(g*Sin[c+d*x])^(p+1)/(2*b*g*(p+1)) /;
FreeQ[{a,b,c,d,e,g,m,p},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && Not[IntegerQ[p]] && EqQ[m+p-1]


Int[(e_.*cos[a_.+b_.*x_])^m_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  -(e*Cos[a+b*x])^m*(g*Sin[c+d*x])^(p+1)/(b*g*m) /;
FreeQ[{a,b,c,d,e,g,m,p},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && Not[IntegerQ[p]] && EqQ[m+2*p+2]


Int[(e_.*sin[a_.+b_.*x_])^m_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  (e*Sin[a+b*x])^m*(g*Sin[c+d*x])^(p+1)/(b*g*m) /;
FreeQ[{a,b,c,d,e,g,m,p},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && Not[IntegerQ[p]] && EqQ[m+2*p+2]


Int[(e_.*cos[a_.+b_.*x_])^m_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  e^2*(e*Cos[a+b*x])^(m-2)*(g*Sin[c+d*x])^(p+1)/(2*b*g*(p+1)) + 
  e^4*(m+p-1)/(4*g^2*(p+1))*Int[(e*Cos[a+b*x])^(m-4)*(g*Sin[c+d*x])^(p+2),x] /;
FreeQ[{a,b,c,d,e,g},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[m,p] && m>2 && p<-1 && 
  (m>3 || p==-3/2) && IntegersQ[2*m,2*p]


Int[(e_.*sin[a_.+b_.*x_])^m_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  -e^2*(e*Sin[a+b*x])^(m-2)*(g*Sin[c+d*x])^(p+1)/(2*b*g*(p+1)) + 
  e^4*(m+p-1)/(4*g^2*(p+1))*Int[(e*Sin[a+b*x])^(m-4)*(g*Sin[c+d*x])^(p+2),x] /;
FreeQ[{a,b,c,d,e,g},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[m,p] && m>2 && p<-1 && 
  (m>3 || p==-3/2) && IntegersQ[2*m,2*p]


Int[(e_.*cos[a_.+b_.*x_])^m_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  (e*Cos[a+b*x])^m*(g*Sin[c+d*x])^(p+1)/(2*b*g*(p+1)) + 
  e^2*(m+2*p+2)/(4*g^2*(p+1))*Int[(e*Cos[a+b*x])^(m-2)*(g*Sin[c+d*x])^(p+2),x] /;
FreeQ[{a,b,c,d,e,g},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[m,p] && m>1 && p<-1 && 
  NeQ[m+2*p+2] && (p<-2 || m==2) && IntegersQ[2*m,2*p]


Int[(e_.*sin[a_.+b_.*x_])^m_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  -(e*Sin[a+b*x])^m*(g*Sin[c+d*x])^(p+1)/(2*b*g*(p+1)) + 
  e^2*(m+2*p+2)/(4*g^2*(p+1))*Int[(e*Sin[a+b*x])^(m-2)*(g*Sin[c+d*x])^(p+2),x] /;
FreeQ[{a,b,c,d,e,g},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[m,p] && m>1 && p<-1 && 
  NeQ[m+2*p+2] && (p<-2 || m==2) && IntegersQ[2*m,2*p]


Int[(e_.*cos[a_.+b_.*x_])^m_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  e^2*(e*Cos[a+b*x])^(m-2)*(g*Sin[c+d*x])^(p+1)/(2*b*g*(m+2*p)) + 
  e^2*(m+p-1)/(m+2*p)*Int[(e*Cos[a+b*x])^(m-2)*(g*Sin[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,e,g,p},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[m] && m>1 && NeQ[m+2*p] &&
  IntegersQ[2*m,2*p]


Int[(e_.*sin[a_.+b_.*x_])^m_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  -e^2*(e*Sin[a+b*x])^(m-2)*(g*Sin[c+d*x])^(p+1)/(2*b*g*(m+2*p)) + 
  e^2*(m+p-1)/(m+2*p)*Int[(e*Sin[a+b*x])^(m-2)*(g*Sin[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,e,g,p},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[m] && m>1 && NeQ[m+2*p] &&
  IntegersQ[2*m,2*p]


Int[(e_.*cos[a_.+b_.*x_])^m_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  -(e*Cos[a+b*x])^m*(g*Sin[c+d*x])^(p+1)/(2*b*g*(m+p+1)) + 
  (m+2*p+2)/(e^2*(m+p+1))*Int[(e*Cos[a+b*x])^(m+2)*(g*Sin[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,e,g,p},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[m] && m<-1 && 
  NeQ[m+2*p+2] && NeQ[m+p+1] && IntegersQ[2*m,2*p]


Int[(e_.*sin[a_.+b_.*x_])^m_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  (e*Sin[a+b*x])^m*(g*Sin[c+d*x])^(p+1)/(2*b*g*(m+p+1)) + 
  (m+2*p+2)/(e^2*(m+p+1))*Int[(e*Sin[a+b*x])^(m+2)*(g*Sin[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,e,g,p},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[m] && m<-1 && 
  NeQ[m+2*p+2] && NeQ[m+p+1] && IntegersQ[2*m,2*p]


Int[cos[a_.+b_.*x_]*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  2*Sin[a+b*x]*(g*Sin[c+d*x])^p/(d*(2*p+1)) + 2*p*g/(2*p+1)*Int[Sin[a+b*x]*(g*Sin[c+d*x])^(p-1),x] /;
FreeQ[{a,b,c,d,g},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[p] && p>0 && IntegerQ[2*p]


Int[sin[a_.+b_.*x_]*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  -2*Cos[a+b*x]*(g*Sin[c+d*x])^p/(d*(2*p+1)) + 2*p*g/(2*p+1)*Int[Cos[a+b*x]*(g*Sin[c+d*x])^(p-1),x] /;
FreeQ[{a,b,c,d,g},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[p] && p>0 && IntegerQ[2*p]


Int[cos[a_.+b_.*x_]*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  Cos[a+b*x]*(g*Sin[c+d*x])^(p+1)/(2*b*g*(p+1)) + 
  (2*p+3)/(2*g*(p+1))*Int[Sin[a+b*x]*(g*Sin[c+d*x])^(p+1),x] /;
FreeQ[{a,b,c,d,g},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[p] && p<-1 && IntegerQ[2*p]


Int[sin[a_.+b_.*x_]*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  -Sin[a+b*x]*(g*Sin[c+d*x])^(p+1)/(2*b*g*(p+1)) + 
  (2*p+3)/(2*g*(p+1))*Int[Cos[a+b*x]*(g*Sin[c+d*x])^(p+1),x] /;
FreeQ[{a,b,c,d,g},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[p] && p<-1 && IntegerQ[2*p]


Int[cos[a_.+b_.*x_]/Sqrt[sin[c_.+d_.*x_]],x_Symbol] :=
  -ArcSin[Cos[a+b*x]-Sin[a+b*x]]/d + Log[Cos[a+b*x]+Sin[a+b*x]+Sqrt[Sin[c+d*x]]]/d /;
FreeQ[{a,b,c,d},x] && EqQ[b*c-a*d] && EqQ[d/b-2]


Int[sin[a_.+b_.*x_]/Sqrt[sin[c_.+d_.*x_]],x_Symbol] :=
  -ArcSin[Cos[a+b*x]-Sin[a+b*x]]/d - Log[Cos[a+b*x]+Sin[a+b*x]+Sqrt[Sin[c+d*x]]]/d /;
FreeQ[{a,b,c,d},x] && EqQ[b*c-a*d] && EqQ[d/b-2]


Int[(g_.*sin[c_.+d_.*x_])^p_/cos[a_.+b_.*x_],x_Symbol] :=
  2*g*Int[Sin[a+b*x]*(g*Sin[c+d*x])^(p-1),x] /;
FreeQ[{a,b,c,d,g,p},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && Not[IntegerQ[p]] && IntegerQ[2*p]


Int[(g_.*sin[c_.+d_.*x_])^p_/sin[a_.+b_.*x_],x_Symbol] :=
  2*g*Int[Cos[a+b*x]*(g*Sin[c+d*x])^(p-1),x] /;
FreeQ[{a,b,c,d,g,p},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && Not[IntegerQ[p]] && IntegerQ[2*p]


(* Int[(e_.*cos[a_.+b_.*x_])^m_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  -(e*Cos[a+b*x])^(m+1)*Sin[a+b*x]*(g*Sin[c+d*x])^p/(b*e*(m+p+1)*(Sin[a+b*x]^2)^((p+1)/2))*
    Hypergeometric2F1[-(p-1)/2,(m+p+1)/2,(m+p+3)/2,Cos[a+b*x]^2] /;
FreeQ[{a,b,c,d,e,g,m,p},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && Not[IntegerQ[p]] && Not[IntegerQ[m+p]] *)


(* Int[(f_.*sin[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  -Cos[a+b*x]*(f*Sin[a+b*x])^(n+1)*(g*Sin[c+d*x])^p/(b*f*(p+1)*(Sin[a+b*x]^2)^((n+p+1)/2))*
    Hypergeometric2F1[-(n+p-1)/2,(p+1)/2,(p+3)/2,Cos[a+b*x]^2] /;
FreeQ[{a,b,c,d,f,g,n,p},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && Not[IntegerQ[p]] && Not[IntegerQ[n+p]] *)


Int[(e_.*cos[a_.+b_.*x_])^m_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  (g*Sin[c+d*x])^p/((e*Cos[a+b*x])^p*Sin[a+b*x]^p)*Int[(e*Cos[a+b*x])^(m+p)*Sin[a+b*x]^p,x] /;
FreeQ[{a,b,c,d,e,g,m,p},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && Not[IntegerQ[p]]


Int[(f_.*sin[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  (g*Sin[c+d*x])^p/(Cos[a+b*x]^p*(f*Sin[a+b*x])^p)*Int[Cos[a+b*x]^p*(f*Sin[a+b*x])^(n+p),x] /;
FreeQ[{a,b,c,d,f,g,n,p},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && Not[IntegerQ[p]]


Int[cos[a_.+b_.*x_]^2*sin[a_.+b_.*x_]^2*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  1/4*Int[(g*Sin[c+d*x])^p,x] - 
  1/4*Int[Cos[c+d*x]^2*(g*Sin[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,g},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && PositiveIntegerQ[p/2]


Int[(e_.*cos[a_.+b_.*x_])^m_.*(f_.*sin[a_.+b_.*x_])^n_.*sin[c_.+d_.*x_]^p_.,x_Symbol] :=
  2^p/(e^p*f^p)*Int[(e*Cos[a+b*x])^(m+p)*(f*Sin[a+b*x])^(n+p),x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && IntegerQ[p]


Int[(e_.*cos[a_.+b_.*x_])^m_.*(f_.*sin[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  e*(e*Cos[a+b*x])^(m-1)*(f*Sin[a+b*x])^(n+1)*(g*Sin[c+d*x])^p/(b*f*(n+p+1)) /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && Not[IntegerQ[p]] && EqQ[m+p+1]


Int[(e_.*sin[a_.+b_.*x_])^m_*(f_.*cos[a_.+b_.*x_])^n_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  -e*(e*Sin[a+b*x])^(m-1)*(f*Cos[a+b*x])^(n+1)*(g*Sin[c+d*x])^p/(b*f*(n+p+1)) /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && Not[IntegerQ[p]] && EqQ[m+p+1]


Int[(e_.*cos[a_.+b_.*x_])^m_.*(f_.*sin[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  -(e*Cos[a+b*x])^(m+1)*(f*Sin[a+b*x])^(n+1)*(g*Sin[c+d*x])^p/(b*e*f*(m+p+1)) /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && Not[IntegerQ[p]] && EqQ[m+n+2*p+2] && NeQ[m+p+1]


Int[(e_.*cos[a_.+b_.*x_])^m_*(f_.*sin[a_.+b_.*x_])^n_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  e^2*(e*Cos[a+b*x])^(m-2)*(f*Sin[a+b*x])^n*(g*Sin[c+d*x])^(p+1)/(2*b*g*(n+p+1)) + 
  e^4*(m+p-1)/(4*g^2*(n+p+1))*Int[(e*Cos[a+b*x])^(m-4)*(f*Sin[a+b*x])^n*(g*Sin[c+d*x])^(p+2),x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[m,p] && m>3 && p<-1 && 
  NeQ[n+p+1] && IntegersQ[2*m,2*n,2*p]


Int[(e_.*sin[a_.+b_.*x_])^m_*(f_.*cos[a_.+b_.*x_])^n_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  -e^2*(e*Sin[a+b*x])^(m-2)*(f*Cos[a+b*x])^n*(g*Sin[c+d*x])^(p+1)/(2*b*g*(n+p+1)) + 
  e^4*(m+p-1)/(4*g^2*(n+p+1))*Int[(e*Sin[a+b*x])^(m-4)*(f*Cos[a+b*x])^n*(g*Sin[c+d*x])^(p+2),x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[m,p] && m>3 && p<-1 && 
  NeQ[n+p+1] && IntegersQ[2*m,2*n,2*p]


Int[(e_.*cos[a_.+b_.*x_])^m_*(f_.*sin[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  (e*Cos[a+b*x])^m*(f*Sin[a+b*x])^n*(g*Sin[c+d*x])^(p+1)/(2*b*g*(n+p+1)) + 
  e^2*(m+n+2*p+2)/(4*g^2*(n+p+1))*Int[(e*Cos[a+b*x])^(m-2)*(f*Sin[a+b*x])^n*(g*Sin[c+d*x])^(p+2),x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[m,p] && m>1 && p<-1 && 
  NeQ[m+n+2*p+2] && NeQ[n+p+1] && IntegersQ[2*m,2*n,2*p] && (p<-2 || m==2 || m==3)


Int[(e_.*sin[a_.+b_.*x_])^m_*(f_.*cos[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  -(e*Sin[a+b*x])^m*(f*Cos[a+b*x])^n*(g*Sin[c+d*x])^(p+1)/(2*b*g*(n+p+1)) + 
  e^2*(m+n+2*p+2)/(4*g^2*(n+p+1))*Int[(e*Sin[a+b*x])^(m-2)*(f*Cos[a+b*x])^n*(g*Sin[c+d*x])^(p+2),x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[m,p] && m>1 && p<-1 && 
  NeQ[m+n+2*p+2] && NeQ[n+p+1] && IntegersQ[2*m,2*n,2*p] && (p<-2 || m==2 || m==3)


Int[(e_.*cos[a_.+b_.*x_])^m_*(f_.*sin[a_.+b_.*x_])^n_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  e*(e*Cos[a+b*x])^(m-1)*(f*Sin[a+b*x])^(n+1)*(g*Sin[c+d*x])^p/(b*f*(n+p+1)) + 
  e^2*(m+p-1)/(f^2*(n+p+1))*Int[(e*Cos[a+b*x])^(m-2)*(f*Sin[a+b*x])^(n+2)*(g*Sin[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,e,f,g,p},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[m,n] && m>1 && n<-1 && 
  NeQ[n+p+1] && IntegersQ[2*m,2*n,2*p]


Int[(e_.*sin[a_.+b_.*x_])^m_*(f_.*cos[a_.+b_.*x_])^n_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  -e*(e*Sin[a+b*x])^(m-1)*(f*Cos[a+b*x])^(n+1)*(g*Sin[c+d*x])^p/(b*f*(n+p+1)) + 
  e^2*(m+p-1)/(f^2*(n+p+1))*Int[(e*Sin[a+b*x])^(m-2)*(f*Cos[a+b*x])^(n+2)*(g*Sin[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,e,f,g,p},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[m,n] && m>1 && n<-1 && 
  NeQ[n+p+1] && IntegersQ[2*m,2*n,2*p]


Int[(e_.*cos[a_.+b_.*x_])^m_*(f_.*sin[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  e*(e*Cos[a+b*x])^(m-1)*(f*Sin[a+b*x])^(n+1)*(g*Sin[c+d*x])^p/(b*f*(m+n+2*p)) + 
  e^2*(m+p-1)/(m+n+2*p)*Int[(e*Cos[a+b*x])^(m-2)*(f*Sin[a+b*x])^n*(g*Sin[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,e,f,g,n,p},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[m] && m>1 && NeQ[m+n+2*p] && 
  IntegersQ[2*m,2*n,2*p]


Int[(e_.*sin[a_.+b_.*x_])^m_*(f_.*cos[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  -e*(e*Sin[a+b*x])^(m-1)*(f*Cos[a+b*x])^(n+1)*(g*Sin[c+d*x])^p/(b*f*(m+n+2*p)) + 
  e^2*(m+p-1)/(m+n+2*p)*Int[(e*Sin[a+b*x])^(m-2)*(f*Cos[a+b*x])^n*(g*Sin[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,e,f,g,n,p},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[m] && m>1 && NeQ[m+n+2*p] && 
  IntegersQ[2*m,2*n,2*p]


Int[(e_.*cos[a_.+b_.*x_])^m_*(f_.*sin[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  -f*(e*Cos[a+b*x])^(m+1)*(f*Sin[a+b*x])^(n-1)*(g*Sin[c+d*x])^p/(b*e*(m+n+2*p)) + 
  2*f*g*(n+p-1)/(e*(m+n+2*p))*Int[(e*Cos[a+b*x])^(m+1)*(f*Sin[a+b*x])^(n-1)*(g*Sin[c+d*x])^(p-1),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[m,n,p] && m<-1 && n>0 && p>0 && 
  NeQ[m+n+2*p] && IntegersQ[2*m,2*n,2*p]


Int[(e_.*sin[a_.+b_.*x_])^m_*(f_.*cos[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  f*(e*Sin[a+b*x])^(m+1)*(f*Cos[a+b*x])^(n-1)*(g*Sin[c+d*x])^p/(b*e*(m+n+2*p)) + 
  2*f*g*(n+p-1)/(e*(m+n+2*p))*Int[(e*Sin[a+b*x])^(m+1)*(f*Cos[a+b*x])^(n-1)*(g*Sin[c+d*x])^(p-1),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[m,n,p] && m<-1 && n>0 && p>0 && 
  NeQ[m+n+2*p] && IntegersQ[2*m,2*n,2*p]


Int[(e_.*cos[a_.+b_.*x_])^m_*(f_.*sin[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  -(e*Cos[a+b*x])^(m+1)*(f*Sin[a+b*x])^(n+1)*(g*Sin[c+d*x])^p/(b*e*f*(m+p+1)) + 
  f*(m+n+2*p+2)/(2*e*g*(m+p+1))*Int[(e*Cos[a+b*x])^(m+1)*(f*Sin[a+b*x])^(n-1)*(g*Sin[c+d*x])^(p+1),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[m,n,p] && m<-1 && n>0 && p<-1 && 
  NeQ[m+n+2*p+2] && NeQ[m+p+1] && IntegersQ[2*m,2*n,2*p]


Int[(e_.*sin[a_.+b_.*x_])^m_*(f_.*cos[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  (e*Sin[a+b*x])^(m+1)*(f*Cos[a+b*x])^(n+1)*(g*Sin[c+d*x])^p/(b*e*f*(m+p+1)) + 
  f*(m+n+2*p+2)/(2*e*g*(m+p+1))*Int[(e*Sin[a+b*x])^(m+1)*(f*Cos[a+b*x])^(n-1)*(g*Sin[c+d*x])^(p+1),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[m,n,p] && m<-1 && n>0 && p<-1 && 
  NeQ[m+n+2*p+2] && NeQ[m+p+1] && IntegersQ[2*m,2*n,2*p]


Int[(e_.*cos[a_.+b_.*x_])^m_*(f_.*sin[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  -(e*Cos[a+b*x])^(m+1)*(f*Sin[a+b*x])^(n+1)*(g*Sin[c+d*x])^p/(b*e*f*(m+p+1)) + 
  (m+n+2*p+2)/(e^2*(m+p+1))*Int[(e*Cos[a+b*x])^(m+2)*(f*Sin[a+b*x])^n*(g*Sin[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,e,f,g,n,p},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[m] && m<-1 && 
  NeQ[m+n+2*p+2] && NeQ[m+p+1] && IntegersQ[2*m,2*n,2*p]


Int[(e_.*sin[a_.+b_.*x_])^m_*(f_.*cos[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  (e*Sin[a+b*x])^(m+1)*(f*Cos[a+b*x])^(n+1)*(g*Sin[c+d*x])^p/(b*e*f*(m+p+1)) + 
  (m+n+2*p+2)/(e^2*(m+p+1))*Int[(e*Sin[a+b*x])^(m+2)*(f*Cos[a+b*x])^n*(g*Sin[c+d*x])^p,x] /;
FreeQ[{a,b,c,d,e,f,g,n,p},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && Not[IntegerQ[p]] && RationalQ[m] && m<-1 && 
  NeQ[m+n+2*p+2] && NeQ[m+p+1] && IntegersQ[2*m,2*n,2*p]


(* Int[(e_.*cos[a_.+b_.*x_])^m_*(f_.*sin[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  -(e*Cos[a+b*x])^(m+1)*(f*Sin[a+b*x])^(n+1)*(g*Sin[c+d*x])^p/(b*e*f*(m+p+1)*(Sin[a+b*x]^2)^((n+p+1)/2))*
    Hypergeometric2F1[-(n+p-1)/2,(m+p+1)/2,(m+p+3)/2,Cos[a+b*x]^2] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && Not[IntegerQ[p]] && Not[IntegerQ[m+p]] && Not[IntegerQ[n+p]] *)


Int[(e_.*cos[a_.+b_.*x_])^m_.*(f_.*sin[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  (g*Sin[c+d*x])^p/((e*Cos[a+b*x])^p*(f*Sin[a+b*x])^p)*Int[(e*Cos[a+b*x])^(m+p)*(f*Sin[a+b*x])^(n+p),x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && EqQ[b*c-a*d] && EqQ[d/b-2] && Not[IntegerQ[p]]


Int[(e_.*cos[a_.+b_.*x_])^m_.*sin[c_.+d_.*x_],x_Symbol] :=
  -(m+2)*(e*Cos[a+b*x])^(m+1)*Cos[(m+1)*(a+b*x)]/(d*e*(m+1)) /;
FreeQ[{a,b,c,d,e,m},x] && EqQ[b*c-a*d] && EqQ[d/b-Abs[m+2]]





(* ::Subsection::Closed:: *)
(*4.4.3 Inert trig functions*)


Int[(a_.*F_[c_.+d_.*x_]^p_)^n_,x_Symbol] :=
  With[{v=ActivateTrig[F[c+d*x]]},
  a^IntPart[n]*(v/NonfreeFactors[v,x])^(p*IntPart[n])*(a*v^p)^FracPart[n]/NonfreeFactors[v,x]^(p*FracPart[n])*
    Int[NonfreeFactors[v,x]^(n*p),x]] /;
FreeQ[{a,c,d,n,p},x] && InertTrigQ[F] && Not[IntegerQ[n]] && IntegerQ[p]


Int[(a_.*(b_.*F_[c_.+d_.*x_])^p_)^n_.,x_Symbol] :=
  With[{v=ActivateTrig[F[c+d*x]]},
  a^IntPart[n]*(a*(b*v)^p)^FracPart[n]/(b*v)^(p*FracPart[n])*Int[(b*v)^(n*p),x]] /;
FreeQ[{a,b,c,d,n,p},x] && InertTrigQ[F] && Not[IntegerQ[n]] && Not[IntegerQ[p]]


Int[u_*F_[c_.*(a_.+b_.*x_)],x_Symbol] :=
  With[{d=FreeFactors[Sin[c*(a+b*x)],x]},
  d/(b*c)*Subst[Int[SubstFor[1,Sin[c*(a+b*x)]/d,u,x],x],x,Sin[c*(a+b*x)]/d] /;
 FunctionOfQ[Sin[c*(a+b*x)]/d,u,x,True]] /;
FreeQ[{a,b,c},x] && (F===Cos || F===cos)


Int[u_*F_[c_.*(a_.+b_.*x_)],x_Symbol] :=
  With[{d=FreeFactors[Cos[c*(a+b*x)],x]},
  -d/(b*c)*Subst[Int[SubstFor[1,Cos[c*(a+b*x)]/d,u,x],x],x,Cos[c*(a+b*x)]/d] /;
 FunctionOfQ[Cos[c*(a+b*x)]/d,u,x,True]] /;
FreeQ[{a,b,c},x] && (F===Sin || F===sin)


Int[u_*F_[c_.*(a_.+b_.*x_)],x_Symbol] :=
  With[{d=FreeFactors[Sin[c*(a+b*x)],x]},
  1/(b*c)*Subst[Int[SubstFor[1/x,Sin[c*(a+b*x)]/d,u,x],x],x,Sin[c*(a+b*x)]/d] /;
 FunctionOfQ[Sin[c*(a+b*x)]/d,u,x,True]] /;
FreeQ[{a,b,c},x] && (F===Cot || F===cot)


Int[u_*F_[c_.*(a_.+b_.*x_)],x_Symbol] :=
  With[{d=FreeFactors[Cos[c*(a+b*x)],x]},
  -1/(b*c)*Subst[Int[SubstFor[1/x,Cos[c*(a+b*x)]/d,u,x],x],x,Cos[c*(a+b*x)]/d] /;
 FunctionOfQ[Cos[c*(a+b*x)]/d,u,x,True]] /;
FreeQ[{a,b,c},x] && (F===Tan || F===tan)


Int[u_*F_[c_.*(a_.+b_.*x_)]^2,x_Symbol] :=
  With[{d=FreeFactors[Tan[c*(a+b*x)],x]},
  d/(b*c)*Subst[Int[SubstFor[1,Tan[c*(a+b*x)]/d,u,x],x],x,Tan[c*(a+b*x)]/d] /;
 FunctionOfQ[Tan[c*(a+b*x)]/d,u,x,True]] /;
FreeQ[{a,b,c},x] && NonsumQ[u] && (F===Sec || F===sec)


Int[u_/cos[c_.*(a_.+b_.*x_)]^2,x_Symbol] :=
  With[{d=FreeFactors[Tan[c*(a+b*x)],x]},
  d/(b*c)*Subst[Int[SubstFor[1,Tan[c*(a+b*x)]/d,u,x],x],x,Tan[c*(a+b*x)]/d] /;
 FunctionOfQ[Tan[c*(a+b*x)]/d,u,x,True]] /;
FreeQ[{a,b,c},x] && NonsumQ[u]


Int[u_*F_[c_.*(a_.+b_.*x_)]^2,x_Symbol] :=
  With[{d=FreeFactors[Cot[c*(a+b*x)],x]},
  -d/(b*c)*Subst[Int[SubstFor[1,Cot[c*(a+b*x)]/d,u,x],x],x,Cot[c*(a+b*x)]/d] /;
 FunctionOfQ[Cot[c*(a+b*x)]/d,u,x,True]] /;
FreeQ[{a,b,c},x] && NonsumQ[u] && (F===Csc || F===csc)


Int[u_/sin[c_.*(a_.+b_.*x_)]^2,x_Symbol] :=
  With[{d=FreeFactors[Cot[c*(a+b*x)],x]},
  -d/(b*c)*Subst[Int[SubstFor[1,Cot[c*(a+b*x)]/d,u,x],x],x,Cot[c*(a+b*x)]/d] /;
 FunctionOfQ[Cot[c*(a+b*x)]/d,u,x,True]] /;
FreeQ[{a,b,c},x] && NonsumQ[u]


Int[u_*F_[c_.*(a_.+b_.*x_)]^n_.,x_Symbol] :=
  With[{d=FreeFactors[Tan[c*(a+b*x)],x]},
  1/(b*c*d^(n-1))*Subst[Int[SubstFor[1/(x^n*(1+d^2*x^2)),Tan[c*(a+b*x)]/d,u,x],x],x,Tan[c*(a+b*x)]/d] /;
 FunctionOfQ[Tan[c*(a+b*x)]/d,u,x,True] && TryPureTanSubst[ActivateTrig[u]*Cot[c*(a+b*x)]^n,x]] /;
FreeQ[{a,b,c},x] && IntegerQ[n] && (F===Cot || F===cot)


Int[u_*F_[c_.*(a_.+b_.*x_)]^n_.,x_Symbol] :=
  With[{d=FreeFactors[Cot[c*(a+b*x)],x]},
  -1/(b*c*d^(n-1))*Subst[Int[SubstFor[1/(x^n*(1+d^2*x^2)),Cot[c*(a+b*x)]/d,u,x],x],x,Cot[c*(a+b*x)]/d] /;
 FunctionOfQ[Cot[c*(a+b*x)]/d,u,x,True] && TryPureTanSubst[ActivateTrig[u]*Tan[c*(a+b*x)]^n,x]] /;
FreeQ[{a,b,c},x] && IntegerQ[n] && (F===Tan || F===tan)


If[ShowSteps,

Int[u_,x_Symbol] :=
  With[{v=FunctionOfTrig[u,x]},
  ShowStep["","Int[F[Cot[a+b*x]],x]","-1/b*Subst[Int[F[x]/(1+x^2),x],x,Cot[a+b*x]]",Hold[
  With[{d=FreeFactors[Cot[v],x]},
  Dist[-d/Coefficient[v,x,1],Subst[Int[SubstFor[1/(1+d^2*x^2),Cot[v]/d,u,x],x],x,Cot[v]/d],x]]]] /;
 Not[FalseQ[v]] && FunctionOfQ[NonfreeFactors[Cot[v],x],u,x,True] && TryPureTanSubst[ActivateTrig[u],x]] /;
SimplifyFlag,

Int[u_,x_Symbol] :=
  With[{v=FunctionOfTrig[u,x]},
  With[{d=FreeFactors[Cot[v],x]},
  Dist[-d/Coefficient[v,x,1],Subst[Int[SubstFor[1/(1+d^2*x^2),Cot[v]/d,u,x],x],x,Cot[v]/d],x]] /;
 Not[FalseQ[v]] && FunctionOfQ[NonfreeFactors[Cot[v],x],u,x,True] && TryPureTanSubst[ActivateTrig[u],x]]]


If[ShowSteps,

Int[u_,x_Symbol] :=
  With[{v=FunctionOfTrig[u,x]},
  ShowStep["","Int[F[Tan[a+b*x]],x]","1/b*Subst[Int[F[x]/(1+x^2),x],x,Tan[a+b*x]]",Hold[
  With[{d=FreeFactors[Tan[v],x]},
  Dist[d/Coefficient[v,x,1],Subst[Int[SubstFor[1/(1+d^2*x^2),Tan[v]/d,u,x],x],x,Tan[v]/d],x]]]] /;
 Not[FalseQ[v]] && FunctionOfQ[NonfreeFactors[Tan[v],x],u,x,True] && TryPureTanSubst[ActivateTrig[u],x]] /;
SimplifyFlag,

Int[u_,x_Symbol] :=
  With[{v=FunctionOfTrig[u,x]},
  With[{d=FreeFactors[Tan[v],x]},
  Dist[d/Coefficient[v,x,1],Subst[Int[SubstFor[1/(1+d^2*x^2),Tan[v]/d,u,x],x],x,Tan[v]/d],x]] /;
 Not[FalseQ[v]] && FunctionOfQ[NonfreeFactors[Tan[v],x],u,x,True] && TryPureTanSubst[ActivateTrig[u],x]]]


Int[F_[a_.+b_.*x_]^p_.*G_[c_.+d_.*x_]^q_.,x_Symbol] :=
  Int[ExpandTrigReduce[ActivateTrig[F[a+b*x]^p*G[c+d*x]^q],x],x] /;
FreeQ[{a,b,c,d},x] && (F===sin || F===cos) && (G===sin || G===cos) && PositiveIntegerQ[p,q]


Int[F_[a_.+b_.*x_]^p_.*G_[c_.+d_.*x_]^q_.*H_[e_.+f_.*x_]^r_.,x_Symbol] :=
  Int[ExpandTrigReduce[ActivateTrig[F[a+b*x]^p*G[c+d*x]^q*H[e+f*x]^r],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && (F===sin || F===cos) && (G===sin || G===cos) && (H===sin || H===cos) && PositiveIntegerQ[p,q,r]


Int[u_*F_[c_.*(a_.+b_.*x_)],x_Symbol] :=
  With[{d=FreeFactors[Sin[c*(a+b*x)],x]},
  d/(b*c)*Subst[Int[SubstFor[1,Sin[c*(a+b*x)]/d,u,x],x],x,Sin[c*(a+b*x)]/d] /;
 FunctionOfQ[Sin[c*(a+b*x)]/d,u,x]] /;
FreeQ[{a,b,c},x] && (F===Cos || F===cos)


Int[u_*F_[c_.*(a_.+b_.*x_)],x_Symbol] :=
  With[{d=FreeFactors[Cos[c*(a+b*x)],x]},
  -d/(b*c)*Subst[Int[SubstFor[1,Cos[c*(a+b*x)]/d,u,x],x],x,Cos[c*(a+b*x)]/d] /;
 FunctionOfQ[Cos[c*(a+b*x)]/d,u,x]] /;
FreeQ[{a,b,c},x] && (F===Sin || F===sin)


Int[u_*F_[c_.*(a_.+b_.*x_)],x_Symbol] :=
  With[{d=FreeFactors[Sin[c*(a+b*x)],x]},
  1/(b*c)*Subst[Int[SubstFor[1/x,Sin[c*(a+b*x)]/d,u,x],x],x,Sin[c*(a+b*x)]/d] /;
 FunctionOfQ[Sin[c*(a+b*x)]/d,u,x]] /;
FreeQ[{a,b,c},x] && (F===Cot || F===cot)


Int[u_*F_[c_.*(a_.+b_.*x_)],x_Symbol] :=
  With[{d=FreeFactors[Cos[c*(a+b*x)],x]},
  -1/(b*c)*Subst[Int[SubstFor[1/x,Cos[c*(a+b*x)]/d,u,x],x],x,Cos[c*(a+b*x)]/d] /;
 FunctionOfQ[Cos[c*(a+b*x)]/d,u,x]] /;
FreeQ[{a,b,c},x] && (F===Tan || F===tan)


Int[u_*F_[c_.*(a_.+b_.*x_)]^n_,x_Symbol] :=
  With[{d=FreeFactors[Sin[c*(a+b*x)],x]},
  d/(b*c)*Subst[Int[SubstFor[(1-d^2*x^2)^((n-1)/2),Sin[c*(a+b*x)]/d,u,x],x],x,Sin[c*(a+b*x)]/d] /;
 FunctionOfQ[Sin[c*(a+b*x)]/d,u,x]] /;
FreeQ[{a,b,c},x] && OddQ[n] && NonsumQ[u] && (F===Cos || F===cos)


Int[u_*F_[c_.*(a_.+b_.*x_)]^n_,x_Symbol] :=
  With[{d=FreeFactors[Sin[c*(a+b*x)],x]},
  d/(b*c)*Subst[Int[SubstFor[(1-d^2*x^2)^((-n-1)/2),Sin[c*(a+b*x)]/d,u,x],x],x,Sin[c*(a+b*x)]/d] /;
 FunctionOfQ[Sin[c*(a+b*x)]/d,u,x]] /;
FreeQ[{a,b,c},x] && OddQ[n] && NonsumQ[u] && (F===Sec || F===sec)


Int[u_*F_[c_.*(a_.+b_.*x_)]^n_,x_Symbol] :=
  With[{d=FreeFactors[Cos[c*(a+b*x)],x]},
  -d/(b*c)*Subst[Int[SubstFor[(1-d^2*x^2)^((n-1)/2),Cos[c*(a+b*x)]/d,u,x],x],x,Cos[c*(a+b*x)]/d] /;
 FunctionOfQ[Cos[c*(a+b*x)]/d,u,x]] /;
FreeQ[{a,b,c},x] && OddQ[n] && NonsumQ[u] && (F===Sin || F===sin)


Int[u_*F_[c_.*(a_.+b_.*x_)]^n_,x_Symbol] :=
  With[{d=FreeFactors[Cos[c*(a+b*x)],x]},
  -d/(b*c)*Subst[Int[SubstFor[(1-d^2*x^2)^((-n-1)/2),Cos[c*(a+b*x)]/d,u,x],x],x,Cos[c*(a+b*x)]/d] /;
 FunctionOfQ[Cos[c*(a+b*x)]/d,u,x]] /;
FreeQ[{a,b,c},x] && OddQ[n] && NonsumQ[u] && (F===Csc || F===csc)


Int[u_*F_[c_.*(a_.+b_.*x_)]^n_,x_Symbol] :=
  With[{d=FreeFactors[Sin[c*(a+b*x)],x]},
  1/(b*c*d^(n-1))*Subst[Int[SubstFor[(1-d^2*x^2)^((n-1)/2)/x^n,Sin[c*(a+b*x)]/d,u,x],x],x,Sin[c*(a+b*x)]/d] /;
 FunctionOfQ[Sin[c*(a+b*x)]/d,u,x]] /;
FreeQ[{a,b,c},x] && OddQ[n] && NonsumQ[u] && (F===Cot || F===cot)


Int[u_*F_[c_.*(a_.+b_.*x_)]^n_,x_Symbol] :=
  With[{d=FreeFactors[Cos[c*(a+b*x)],x]},
  -1/(b*c*d^(n-1))*Subst[Int[SubstFor[(1-d^2*x^2)^((n-1)/2)/x^n,Cos[c*(a+b*x)]/d,u,x],x],x,Cos[c*(a+b*x)]/d] /;
 FunctionOfQ[Cos[c*(a+b*x)]/d,u,x]] /;
FreeQ[{a,b,c},x] && OddQ[n] && NonsumQ[u] && (F===Tan || F===tan)


Int[u_*(v_+d_.*F_[c_.*(a_.+b_.*x_)]^n_.),x_Symbol] :=
  With[{e=FreeFactors[Sin[c*(a+b*x)],x]},
  Int[ActivateTrig[u*v],x] + d*Int[ActivateTrig[u]*Cos[c*(a+b*x)]^n,x] /;
 FunctionOfQ[Sin[c*(a+b*x)]/e,u,x]] /;
FreeQ[{a,b,c,d},x] && Not[FreeQ[v,x]] && OddQ[n] && NonsumQ[u] && (F===Cos || F===cos)


Int[u_*(v_+d_.*F_[c_.*(a_.+b_.*x_)]^n_.),x_Symbol] :=
  With[{e=FreeFactors[Cos[c*(a+b*x)],x]},
  Int[ActivateTrig[u*v],x] + d*Int[ActivateTrig[u]*Sin[c*(a+b*x)]^n,x] /;
 FunctionOfQ[Cos[c*(a+b*x)]/e,u,x]] /;
FreeQ[{a,b,c,d},x] && Not[FreeQ[v,x]] && OddQ[n] && NonsumQ[u] && (F===Sin || F===sin)


If[ShowSteps,

Int[u_,x_Symbol] :=
  With[{v=FunctionOfTrig[u,x]},
  ShowStep["","Int[F[Sin[a+b*x]]*Cos[a+b*x],x]","Subst[Int[F[x],x],x,Sin[a+b*x]]/b",Hold[
  With[{d=FreeFactors[Sin[v],x]},
  Dist[d/Coefficient[v,x,1],Subst[Int[SubstFor[1,Sin[v]/d,u/Cos[v],x],x],x,Sin[v]/d],x]]]] /;
 Not[FalseQ[v]] && FunctionOfQ[NonfreeFactors[Sin[v],x],u/Cos[v],x]] /;
SimplifyFlag,

Int[u_,x_Symbol] :=
  With[{v=FunctionOfTrig[u,x]},
  With[{d=FreeFactors[Sin[v],x]},
  Dist[d/Coefficient[v,x,1],Subst[Int[SubstFor[1,Sin[v]/d,u/Cos[v],x],x],x,Sin[v]/d],x]] /;
 Not[FalseQ[v]] && FunctionOfQ[NonfreeFactors[Sin[v],x],u/Cos[v],x]]]


If[ShowSteps,

Int[u_,x_Symbol] :=
  With[{v=FunctionOfTrig[u,x]},
  ShowStep["","Int[F[Cos[a+b*x]]*Sin[a+b*x],x]","-Subst[Int[F[x],x],x,Cos[a+b*x]]/b",Hold[
  With[{d=FreeFactors[Cos[v],x]},
  Dist[-d/Coefficient[v,x,1],Subst[Int[SubstFor[1,Cos[v]/d,u/Sin[v],x],x],x,Cos[v]/d],x]]]] /;
 Not[FalseQ[v]] && FunctionOfQ[NonfreeFactors[Cos[v],x],u/Sin[v],x]] /;
SimplifyFlag,

Int[u_,x_Symbol] :=
  With[{v=FunctionOfTrig[u,x]},
  With[{d=FreeFactors[Cos[v],x]},
  Dist[-d/Coefficient[v,x,1],Subst[Int[SubstFor[1,Cos[v]/d,u/Sin[v],x],x],x,Cos[v]/d],x]] /;
 Not[FalseQ[v]] && FunctionOfQ[NonfreeFactors[Cos[v],x],u/Sin[v],x]]]


Int[u_.*(a_.+b_.*cos[d_.+e_.*x_]^2+c_.*sin[d_.+e_.*x_]^2)^p_.,x_Symbol] :=
  (a+c)^p*Int[ActivateTrig[u],x] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[b-c]


Int[u_.*(a_.+b_.*tan[d_.+e_.*x_]^2+c_.*sec[d_.+e_.*x_]^2)^p_.,x_Symbol] :=
  (a+c)^p*Int[ActivateTrig[u],x] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[b+c]


Int[u_.*(a_.+b_.*cot[d_.+e_.*x_]^2+c_.*csc[d_.+e_.*x_]^2)^p_.,x_Symbol] :=
  (a+c)^p*Int[ActivateTrig[u],x] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[b+c]


Int[u_/y_,x_Symbol] :=
  With[{q=DerivativeDivides[ActivateTrig[y],ActivateTrig[u],x]},
    q*Log[RemoveContent[ActivateTrig[y],x]] /;
 Not[FalseQ[q]]] /;
Not[InertTrigFreeQ[u]]


Int[u_/(y_*w_),x_Symbol] :=
  With[{q=DerivativeDivides[ActivateTrig[y*w],ActivateTrig[u],x]},
    q*Log[RemoveContent[ActivateTrig[y*w],x]] /;
 Not[FalseQ[q]]] /;
Not[InertTrigFreeQ[u]]


Int[u_*y_^m_.,x_Symbol] :=
  With[{q=DerivativeDivides[ActivateTrig[y],ActivateTrig[u],x]},
   q*ActivateTrig[y^(m+1)]/(m+1) /;
 Not[FalseQ[q]]] /;
FreeQ[m,x] && NeQ[m+1] && Not[InertTrigFreeQ[u]]


Int[u_*y_^m_.*z_^n_.,x_Symbol] :=
  With[{q=DerivativeDivides[ActivateTrig[y*z],ActivateTrig[u*z^(n-m)],x]},
   q*ActivateTrig[y^(m+1)*z^(m+1)]/(m+1) /;
 Not[FalseQ[q]]] /;
FreeQ[{m,n},x] && NeQ[m+1] && Not[InertTrigFreeQ[u]]


Int[u_.*(a_.*F_[c_.+d_.*x_]^p_)^n_,x_Symbol] :=
  With[{v=ActivateTrig[F[c+d*x]]},
  a^IntPart[n]*(v/NonfreeFactors[v,x])^(p*IntPart[n])*(a*v^p)^FracPart[n]/NonfreeFactors[v,x]^(p*FracPart[n])*
    Int[ActivateTrig[u]*NonfreeFactors[v,x]^(n*p),x]] /;
FreeQ[{a,c,d,n,p},x] && InertTrigQ[F] && Not[IntegerQ[n]] && IntegerQ[p]


Int[u_.*(a_.*(b_.*F_[c_.+d_.*x_])^p_)^n_.,x_Symbol] :=
  With[{v=ActivateTrig[F[c+d*x]]},
  a^IntPart[n]*(a*(b*v)^p)^FracPart[n]/(b*v)^(p*FracPart[n])*Int[ActivateTrig[u]*(b*v)^(n*p),x]] /;
FreeQ[{a,b,c,d,n,p},x] && InertTrigQ[F] && Not[IntegerQ[n]] && Not[IntegerQ[p]]


If[ShowSteps,

Int[u_,x_Symbol] :=
  With[{v=FunctionOfTrig[u,x]},
  ShowStep["","Int[F[Tan[a+b*x]],x]","1/b*Subst[Int[F[x]/(1+x^2),x],x,Tan[a+b*x]]",Hold[
  With[{d=FreeFactors[Tan[v],x]},
  Dist[d/Coefficient[v,x,1],Subst[Int[SubstFor[1/(1+d^2*x^2),Tan[v]/d,u,x],x],x,Tan[v]/d],x]]]] /;
 Not[FalseQ[v]] && FunctionOfQ[NonfreeFactors[Tan[v],x],u,x]] /;
SimplifyFlag && InverseFunctionFreeQ[u,x],

Int[u_,x_Symbol] :=
  With[{v=FunctionOfTrig[u,x]},
  With[{d=FreeFactors[Tan[v],x]},
  Dist[d/Coefficient[v,x,1],Subst[Int[SubstFor[1/(1+d^2*x^2),Tan[v]/d,u,x],x],x,Tan[v]/d],x]] /;
 Not[FalseQ[v]] && FunctionOfQ[NonfreeFactors[Tan[v],x],u,x]] /;
InverseFunctionFreeQ[u,x]]


Int[u_.*(a_.*tan[c_.+d_.*x_]^n_.+b_.*sec[c_.+d_.*x_]^n_.)^p_,x_Symbol] :=
  Int[ActivateTrig[u]*Sec[c+d*x]^(n*p)*(b+a*Sin[c+d*x]^n)^p,x] /;
FreeQ[{a,b,c,d},x] && IntegersQ[n,p]


Int[u_.*(a_.*cot[c_.+d_.*x_]^n_.+b_.*csc[c_.+d_.*x_]^n_.)^p_,x_Symbol] :=
  Int[ActivateTrig[u]*Csc[c+d*x]^(n*p)*(b+a*Cos[c+d*x]^n)^p,x] /;
FreeQ[{a,b,c,d},x] && IntegersQ[n,p]


Int[u_*(a_*F_[c_.+d_.*x_]^p_.+b_.*F_[c_.+d_.*x_]^q_.)^n_.,x_Symbol] :=
  Int[ActivateTrig[u*F[c+d*x]^(n*p)*(a+b*F[c+d*x]^(q-p))^n],x] /;
FreeQ[{a,b,c,d,p,q},x] && InertTrigQ[F] && IntegerQ[n] && PosQ[q-p]


Int[u_*(a_*F_[d_.+e_.*x_]^p_.+b_.*F_[d_.+e_.*x_]^q_.+c_.*F_[d_.+e_.*x_]^r_.)^n_.,x_Symbol] :=
  Int[ActivateTrig[u*F[d+e*x]^(n*p)*(a+b*F[d+e*x]^(q-p)+c*F[d+e*x]^(r-p))^n],x] /;
FreeQ[{a,b,c,d,e,p,q,r},x] && InertTrigQ[F] && IntegerQ[n] && PosQ[q-p] && PosQ[r-p]


Int[u_*(a_+b_.*F_[d_.+e_.*x_]^p_.+c_.*F_[d_.+e_.*x_]^q_.)^n_.,x_Symbol] :=
  Int[ActivateTrig[u*F[d+e*x]^(n*p)*(b+a*F[d+e*x]^(-p)+c*F[d+e*x]^(q-p))^n],x] /;
FreeQ[{a,b,c,d,e,p,q},x] && InertTrigQ[F] && IntegerQ[n] && NegQ[p]


Int[u_.*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[ActivateTrig[u]*(a*E^(-a/b*(c+d*x)))^n,x] /;
FreeQ[{a,b,c,d,n},x] && EqQ[a^2+b^2]


Int[u_,x_Symbol] :=
  Int[TrigSimplify[u],x] /;
TrigSimplifyQ[u]


Int[u_.*(a_*v_)^p_,x_Symbol] :=
  With[{uu=ActivateTrig[u],vv=ActivateTrig[v]},
  a^IntPart[p]*(a*vv)^FracPart[p]/(vv^FracPart[p])*Int[uu*vv^p,x]] /;
FreeQ[{a,p},x] && Not[IntegerQ[p]] && Not[InertTrigFreeQ[v]]


Int[u_.*(v_^m_)^p_,x_Symbol] :=
  With[{uu=ActivateTrig[u],vv=ActivateTrig[v]},
  (vv^m)^FracPart[p]/(vv^(m*FracPart[p]))*Int[uu*vv^(m*p),x]] /;
FreeQ[{m,p},x] && Not[IntegerQ[p]] && Not[InertTrigFreeQ[v]]


Int[u_.*(v_^m_.*w_^n_.)^p_,x_Symbol] :=
  With[{uu=ActivateTrig[u],vv=ActivateTrig[v],ww=ActivateTrig[w]},
  (vv^m*ww^n)^FracPart[p]/(vv^(m*FracPart[p])*ww^(n*FracPart[p]))*Int[uu*vv^(m*p)*ww^(n*p),x]] /;
FreeQ[{m,n,p},x] && Not[IntegerQ[p]] && (Not[InertTrigFreeQ[v]] || Not[InertTrigFreeQ[w]])


Int[u_,x_Symbol] :=
  With[{v=ExpandTrig[u,x]},
  Int[v,x] /;
 SumQ[v]] /;
Not[InertTrigFreeQ[u]]


If[ShowSteps,

Int[u_,x_Symbol] :=
  With[{w=Block[{ShowSteps=False,$StepCounter=Null}, 
			Int[SubstFor[1/(1+FreeFactors[Tan[FunctionOfTrig[u,x]/2],x]^2*x^2),Tan[FunctionOfTrig[u,x]/2]/FreeFactors[Tan[FunctionOfTrig[u,x]/2],x],u,x],x]]},  
  ShowStep["","Int[F[Sin[a+b*x],Cos[a+b*x]],x]","2/b*Subst[Int[1/(1+x^2)*F[2*x/(1+x^2),(1-x^2)/(1+x^2)],x],x,Tan[(a+b*x)/2]]",Hold[
  Module[{v=FunctionOfTrig[u,x],d},
  d=FreeFactors[Tan[v/2],x];
  Dist[2*d/Coefficient[v,x,1],Subst[Int[SubstFor[1/(1+d^2*x^2),Tan[v/2]/d,u,x],x],x,Tan[v/2]/d],x]]]] /;
 FreeQ[w,Int]] /;
SimplifyFlag && InverseFunctionFreeQ[u,x] && Not[FalseQ[FunctionOfTrig[u,x]]],

Int[u_,x_Symbol] :=
  With[{w=Block[{ShowSteps=False,$StepCounter=Null}, 
			Int[SubstFor[1/(1+FreeFactors[Tan[FunctionOfTrig[u,x]/2],x]^2*x^2),Tan[FunctionOfTrig[u,x]/2]/FreeFactors[Tan[FunctionOfTrig[u,x]/2],x],u,x],x]]},  
  Module[{v=FunctionOfTrig[u,x],d},
  d=FreeFactors[Tan[v/2],x];
  Dist[2*d/Coefficient[v,x,1],Subst[Int[SubstFor[1/(1+d^2*x^2),Tan[v/2]/d,u,x],x],x,Tan[v/2]/d],x]] /;
 FreeQ[w,Int]] /;
InverseFunctionFreeQ[u,x] && Not[FalseQ[FunctionOfTrig[u,x]]]]


(* If[ShowSteps,

Int[u_,x_Symbol] :=
  With[{v=FunctionOfTrig[u,x]},
  ShowStep["","Int[F[Sin[a+b*x],Cos[a+b*x]],x]","2/b*Subst[Int[1/(1+x^2)*F[2*x/(1+x^2),(1-x^2)/(1+x^2)],x],x,Tan[(a+b*x)/2]]",Hold[
  With[{d=FreeFactors[Tan[v/2],x]},
  Dist[2*d/Coefficient[v,x,1],Subst[Int[SubstFor[1/(1+d^2*x^2),Tan[v/2]/d,u,x],x],x,Tan[v/2]/d],x]]]] /;
 Not[FalseQ[v]]] /;
SimplifyFlag && InverseFunctionFreeQ[u,x],

Int[u_,x_Symbol] :=
  With[{v=FunctionOfTrig[u,x]},
  With[{d=FreeFactors[Tan[v/2],x]},
  Dist[2*d/Coefficient[v,x,1],Subst[Int[SubstFor[1/(1+d^2*x^2),Tan[v/2]/d,u,x],x],x,Tan[v/2]/d],x]] /;
 Not[FalseQ[v]]] /;
InverseFunctionFreeQ[u,x]] *)


Int[u_,x_Symbol] :=
  With[{v=ActivateTrig[u]},
   Defer[Int][v,x]] /;
Not[InertTrigFreeQ[u]]





(* ::Subsection::Closed:: *)
(*4.4.5 (c+d x)^m trig(a+b x)^n trig(a+b x)^p*)


Int[(c_.+d_.*x_)^m_.*Sin[a_.+b_.*x_]^n_.*Cos[a_.+b_.*x_],x_Symbol] :=
  (c+d*x)^m*Sin[a+b*x]^(n+1)/(b*(n+1)) - 
  d*m/(b*(n+1))*Int[(c+d*x)^(m-1)*Sin[a+b*x]^(n+1),x] /;
FreeQ[{a,b,c,d,n},x] && PositiveIntegerQ[m] && NeQ[n+1]


Int[(c_.+d_.*x_)^m_.*Sin[a_.+b_.*x_]*Cos[a_.+b_.*x_]^n_.,x_Symbol] :=
  -(c+d*x)^m*Cos[a+b*x]^(n+1)/(b*(n+1)) + 
  d*m/(b*(n+1))*Int[(c+d*x)^(m-1)*Cos[a+b*x]^(n+1),x] /;
FreeQ[{a,b,c,d,n},x] && PositiveIntegerQ[m] && NeQ[n+1]


Int[(c_.+d_.*x_)^m_.*Sin[a_.+b_.*x_]^n_.*Cos[a_.+b_.*x_]^p_.,x_Symbol] :=
  Int[ExpandTrigReduce[(c+d*x)^m,Sin[a+b*x]^n*Cos[a+b*x]^p,x],x] /;
FreeQ[{a,b,c,d,m},x] && PositiveIntegerQ[n,p]


Int[(c_.+d_.*x_)^m_.*Sin[a_.+b_.*x_]^n_.*Tan[a_.+b_.*x_]^p_.,x_Symbol] :=
  -Int[(c+d*x)^m*Sin[a+b*x]^n*Tan[a+b*x]^(p-2),x] + Int[(c+d*x)^m*Sin[a+b*x]^(n-2)*Tan[a+b*x]^p,x] /;
FreeQ[{a,b,c,d,m},x] && PositiveIntegerQ[n,p]


Int[(c_.+d_.*x_)^m_.*Cos[a_.+b_.*x_]^n_.*Cot[a_.+b_.*x_]^p_.,x_Symbol] :=
  -Int[(c+d*x)^m*Cos[a+b*x]^n*Cot[a+b*x]^(p-2),x] + Int[(c+d*x)^m*Cos[a+b*x]^(n-2)*Cot[a+b*x]^p,x] /;
FreeQ[{a,b,c,d,m},x] && PositiveIntegerQ[n,p]


Int[(c_.+d_.*x_)^m_.*Sec[a_.+b_.*x_]^n_.*Tan[a_.+b_.*x_]^p_.,x_Symbol] :=
  (c+d*x)^m*Sec[a+b*x]^n/(b*n) - 
  d*m/(b*n)*Int[(c+d*x)^(m-1)*Sec[a+b*x]^n,x] /;
FreeQ[{a,b,c,d,n},x] && p===1 && RationalQ[m] && m>0


Int[(c_.+d_.*x_)^m_.*Csc[a_.+b_.*x_]^n_.*Cot[a_.+b_.*x_]^p_.,x_Symbol] :=
  -(c+d*x)^m*Csc[a+b*x]^n/(b*n) + 
  d*m/(b*n)*Int[(c+d*x)^(m-1)*Csc[a+b*x]^n,x] /;
FreeQ[{a,b,c,d,n},x] && p===1 && RationalQ[m] && m>0


Int[(c_.+d_.*x_)^m_.*Sec[a_.+b_.*x_]^2*Tan[a_.+b_.*x_]^n_.,x_Symbol] :=
  (c+d*x)^m*Tan[a+b*x]^(n+1)/(b*(n+1)) - 
  d*m/(b*(n +1))*Int[(c+d*x)^(m-1)*Tan[a+b*x]^(n+1),x] /;
FreeQ[{a,b,c,d,n},x] && PositiveIntegerQ[m] && NeQ[n+1]


Int[(c_.+d_.*x_)^m_.*Csc[a_.+b_.*x_]^2*Cot[a_.+b_.*x_]^n_.,x_Symbol] :=
  -(c+d*x)^m*Cot[a+b*x]^(n+1)/(b*(n+1)) + 
  d*m/(b*(n +1))*Int[(c+d*x)^(m-1)*Cot[a+b*x]^(n+1),x] /;
FreeQ[{a,b,c,d,n},x] && PositiveIntegerQ[m] && NeQ[n+1]


Int[(c_.+d_.*x_)^m_.*Sec[a_.+b_.*x_]*Tan[a_.+b_.*x_]^p_,x_Symbol] :=
  -Int[(c+d*x)^m*Sec[a+b*x]*Tan[a+b*x]^(p-2),x] + Int[(c+d*x)^m*Sec[a+b*x]^3*Tan[a+b*x]^(p-2),x] /;
FreeQ[{a,b,c,d,m},x] && PositiveIntegerQ[p/2]


Int[(c_.+d_.*x_)^m_.*Sec[a_.+b_.*x_]^n_.*Tan[a_.+b_.*x_]^p_,x_Symbol] :=
  -Int[(c+d*x)^m*Sec[a+b*x]^n*Tan[a+b*x]^(p-2),x] + Int[(c+d*x)^m*Sec[a+b*x]^(n+2)*Tan[a+b*x]^(p-2),x] /;
FreeQ[{a,b,c,d,m,n},x] && PositiveIntegerQ[p/2]


Int[(c_.+d_.*x_)^m_.*Csc[a_.+b_.*x_]*Cot[a_.+b_.*x_]^p_,x_Symbol] :=
  -Int[(c+d*x)^m*Csc[a+b*x]*Cot[a+b*x]^(p-2),x] + Int[(c+d*x)^m*Csc[a+b*x]^3*Cot[a+b*x]^(p-2),x] /;
FreeQ[{a,b,c,d,m},x] && PositiveIntegerQ[p/2]


Int[(c_.+d_.*x_)^m_.*Csc[a_.+b_.*x_]^n_.*Cot[a_.+b_.*x_]^p_,x_Symbol] :=
  -Int[(c+d*x)^m*Csc[a+b*x]^n*Cot[a+b*x]^(p-2),x] + Int[(c+d*x)^m*Csc[a+b*x]^(n+2)*Cot[a+b*x]^(p-2),x] /;
FreeQ[{a,b,c,d,m,n},x] && PositiveIntegerQ[p/2]


Int[(c_.+d_.*x_)^m_.*Sec[a_.+b_.*x_]^n_.*Tan[a_.+b_.*x_]^p_.,x_Symbol] :=
  Module[{u=IntHide[Sec[a+b*x]^n*Tan[a+b*x]^p,x]},
  Dist[(c+d*x)^m,u,x] - d*m*Int[(c+d*x)^(m-1)*u,x]] /;
FreeQ[{a,b,c,d,n,p},x] && PositiveIntegerQ[m] && (EvenQ[n] || OddQ[p])


Int[(c_.+d_.*x_)^m_.*Csc[a_.+b_.*x_]^n_.*Cot[a_.+b_.*x_]^p_.,x_Symbol] :=
  Module[{u=IntHide[Csc[a+b*x]^n*Cot[a+b*x]^p,x]},
  Dist[(c+d*x)^m,u,x] - d*m*Int[(c+d*x)^(m-1)*u,x]] /;
FreeQ[{a,b,c,d,n,p},x] && PositiveIntegerQ[m] && (EvenQ[n] || OddQ[p])


Int[(c_.+d_.*x_)^m_.*Csc[a_.+b_.*x_]^n_.*Sec[a_.+b_.*x_]^n_., x_Symbol] :=
  2^n*Int[(c+d*x)^m*Csc[2*a+2*b*x]^n,x] /;
FreeQ[{a,b,c,d},x] && RationalQ[m] && IntegerQ[n]


Int[(c_.+d_.*x_)^m_.*Csc[a_.+b_.*x_]^n_.*Sec[a_.+b_.*x_]^p_., x_Symbol] :=
  Module[{u=IntHide[Csc[a+b*x]^n*Sec[a+b*x]^p,x]},
  Dist[(c+d*x)^m,u,x] - d*m*Int[(c+d*x)^(m-1)*u,x]] /;
FreeQ[{a,b,c,d},x] && IntegersQ[n,p] && RationalQ[m] && m>0 && n!=p


Int[u_^m_.*F_[v_]^n_.*G_[w_]^p_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*F[ExpandToSum[v,x]]^n*G[ExpandToSum[v,x]]^p,x] /;
FreeQ[{m,n,p},x] && TrigQ[F] && TrigQ[G] && EqQ[v-w] && LinearQ[{u,v,w},x] && Not[LinearMatchQ[{u,v,w},x]]


Int[(e_.+f_.*x_)^m_.*Cos[c_.+d_.*x_]*(a_+b_.*Sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e+f*x)^m*(a+b*Sin[c+d*x])^(n+1)/(b*d*(n+1)) - 
  f*m/(b*d*(n+1))*Int[(e+f*x)^(m-1)*(a+b*Sin[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && PositiveIntegerQ[m] && NeQ[n+1]


Int[(e_.+f_.*x_)^m_.*Sin[c_.+d_.*x_]*(a_+b_.*Cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  -(e+f*x)^m*(a+b*Cos[c+d*x])^(n+1)/(b*d*(n+1)) + 
  f*m/(b*d*(n+1))*Int[(e+f*x)^(m-1)*(a+b*Cos[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && PositiveIntegerQ[m] && NeQ[n+1]


Int[(e_.+f_.*x_)^m_.*Sec[c_.+d_.*x_]^2*(a_+b_.*Tan[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e+f*x)^m*(a+b*Tan[c+d*x])^(n+1)/(b*d*(n+1)) - 
  f*m/(b*d*(n+1))*Int[(e+f*x)^(m-1)*(a+b*Tan[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && PositiveIntegerQ[m] && NeQ[n+1]


Int[(e_.+f_.*x_)^m_.*Csc[c_.+d_.*x_]^2*(a_+b_.*Cot[c_.+d_.*x_])^n_.,x_Symbol] :=
  -(e+f*x)^m*(a+b*Cot[c+d*x])^(n+1)/(b*d*(n+1)) + 
  f*m/(b*d*(n+1))*Int[(e+f*x)^(m-1)*(a+b*Cot[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && PositiveIntegerQ[m] && NeQ[n+1]


Int[(e_.+f_.*x_)^m_.*Sec[c_.+d_.*x_]*Tan[c_.+d_.*x_]*(a_+b_.*Sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e+f*x)^m*(a+b*Sec[c+d*x])^(n+1)/(b*d*(n+1)) - 
  f*m/(b*d*(n+1))*Int[(e+f*x)^(m-1)*(a+b*Sec[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && PositiveIntegerQ[m] && NeQ[n+1]


Int[(e_.+f_.*x_)^m_.*Csc[c_.+d_.*x_]*Cot[c_.+d_.*x_]*(a_+b_.*Csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  -(e+f*x)^m*(a+b*Csc[c+d*x])^(n+1)/(b*d*(n+1)) + 
  f*m/(b*d*(n+1))*Int[(e+f*x)^(m-1)*(a+b*Csc[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && PositiveIntegerQ[m] && NeQ[n+1]


Int[(e_.+f_.*x_)^m_.*Sin[a_.+b_.*x_]^p_.*Sin[c_.+d_.*x_]^q_.,x_Symbol] :=
  Int[ExpandTrigReduce[(e+f*x)^m,Sin[a+b*x]^p*Sin[c+d*x]^q,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveIntegerQ[p,q] && IntegerQ[m]


Int[(e_.+f_.*x_)^m_.*Cos[a_.+b_.*x_]^p_.*Cos[c_.+d_.*x_]^q_.,x_Symbol] :=
  Int[ExpandTrigReduce[(e+f*x)^m,Cos[a+b*x]^p*Cos[c+d*x]^q,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveIntegerQ[p,q] && IntegerQ[m]


Int[(e_.+f_.*x_)^m_.*Sin[a_.+b_.*x_]^p_.*Cos[c_.+d_.*x_]^q_.,x_Symbol] :=
  Int[ExpandTrigReduce[(e+f*x)^m,Sin[a+b*x]^p*Cos[c+d*x]^q,x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && PositiveIntegerQ[p,q]


Int[(e_.+f_.*x_)^m_.*F_[a_.+b_.*x_]^p_.*G_[c_.+d_.*x_]^q_.,x_Symbol] :=
  Int[ExpandTrigExpand[(e+f*x)^m*G[c+d*x]^q,F,c+d*x,p,b/d,x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && MemberQ[{Sin,Cos},F] && MemberQ[{Sec,Csc},G] && 
  PositiveIntegerQ[p,q] && EqQ[b*c-a*d] && PositiveIntegerQ[b/d-1]





(* ::Subsection::Closed:: *)
(*4.4.6 F^(c (a+b x)) trig(d+e x)^n*)


Int[F_^(c_.*(a_.+b_.*x_))*Sin[d_.+e_.*x_],x_Symbol] :=
  b*c*Log[F]*F^(c*(a+b*x))*Sin[d+e*x]/(e^2+b^2*c^2*Log[F]^2) - 
  e*F^(c*(a+b*x))*Cos[d+e*x]/(e^2+b^2*c^2*Log[F]^2) /;
FreeQ[{F,a,b,c,d,e},x] && NeQ[e^2+b^2*c^2*Log[F]^2]


Int[F_^(c_.*(a_.+b_.*x_))*Cos[d_.+e_.*x_],x_Symbol] :=
  b*c*Log[F]*F^(c*(a+b*x))*Cos[d+e*x]/(e^2+b^2*c^2*Log[F]^2) + 
  e*F^(c*(a+b*x))*Sin[d+e*x]/(e^2+b^2*c^2*Log[F]^2) /;
FreeQ[{F,a,b,c,d,e},x] && NeQ[e^2+b^2*c^2*Log[F]^2]


Int[F_^(c_.*(a_.+b_.*x_))*Sin[d_.+e_.*x_]^n_,x_Symbol] :=
  b*c*Log[F]*F^(c*(a+b*x))*Sin[d+e*x]^n/(e^2*n^2+b^2*c^2*Log[F]^2) - 
  e*n*F^(c*(a+b*x))*Cos[d+e*x]*Sin[d+e*x]^(n-1)/(e^2*n^2+b^2*c^2*Log[F]^2) + 
  (n*(n-1)*e^2)/(e^2*n^2+b^2*c^2*Log[F]^2)*Int[F^(c*(a+b*x))*Sin[d+e*x]^(n-2),x] /;
FreeQ[{F,a,b,c,d,e},x] && NeQ[e^2*n^2+b^2*c^2*Log[F]^2] && RationalQ[n] && n>1


Int[F_^(c_.*(a_.+b_.*x_))*Cos[d_.+e_.*x_]^m_,x_Symbol] :=
  b*c*Log[F]*F^(c*(a+b*x))*Cos[d+e*x]^m/(e^2*m^2+b^2*c^2*Log[F]^2) + 
  e*m*F^(c*(a+b*x))*Sin[d+e*x]*Cos[d+e*x]^(m-1)/(e^2*m^2+b^2*c^2*Log[F]^2) + 
  (m*(m-1)*e^2)/(e^2*m^2+b^2*c^2*Log[F]^2)*Int[F^(c*(a+b*x))*Cos[d+e*x]^(m-2),x] /;
FreeQ[{F,a,b,c,d,e},x] && NeQ[e^2*m^2+b^2*c^2*Log[F]^2] && RationalQ[m] && m>1


Int[F_^(c_.*(a_.+b_.*x_))*Sin[d_.+e_.*x_]^n_,x_Symbol] :=
  -b*c*Log[F]*F^(c*(a+b*x))*Sin[d+e*x]^(n+2)/(e^2*(n+1)*(n+2)) + 
  F^(c*(a+b*x))*Cos[d+e*x]*Sin[d+e*x]^(n+1)/(e*(n+1)) /;
FreeQ[{F,a,b,c,d,e,n},x] && EqQ[e^2*(n+2)^2+b^2*c^2*Log[F]^2] && NeQ[n+1] && NeQ[n+2]


Int[F_^(c_.*(a_.+b_.*x_))*Cos[d_.+e_.*x_]^n_,x_Symbol] :=
  -b*c*Log[F]*F^(c*(a+b*x))*Cos[d+e*x]^(n+2)/(e^2*(n+1)*(n+2)) - 
  F^(c*(a+b*x))*Sin[d+e*x]*Cos[d+e*x]^(n+1)/(e*(n+1)) /;
FreeQ[{F,a,b,c,d,e,n},x] && EqQ[e^2*(n+2)^2+b^2*c^2*Log[F]^2] && NeQ[n+1] && NeQ[n+2]


Int[F_^(c_.*(a_.+b_.*x_))*Sin[d_.+e_.*x_]^n_,x_Symbol] :=
  -b*c*Log[F]*F^(c*(a+b*x))*Sin[d+e*x]^(n+2)/(e^2*(n+1)*(n+2)) + 
  F^(c*(a+b*x))*Cos[d+e*x]*Sin[d+e*x]^(n+1)/(e*(n+1)) + 
  (e^2*(n+2)^2+b^2*c^2*Log[F]^2)/(e^2*(n+1)*(n+2))*Int[F^(c*(a+b*x))*Sin[d+e*x]^(n+2),x] /;
FreeQ[{F,a,b,c,d,e},x] && NeQ[e^2*(n+2)^2+b^2*c^2*Log[F]^2] && RationalQ[n] && n<-1 && n!=-2


Int[F_^(c_.*(a_.+b_.*x_))*Cos[d_.+e_.*x_]^n_,x_Symbol] :=
  -b*c*Log[F]*F^(c*(a+b*x))*Cos[d+e*x]^(n+2)/(e^2*(n+1)*(n+2)) - 
  F^(c*(a+b*x))*Sin[d+e*x]*Cos[d+e*x]^(n+1)/(e*(n+1)) + 
  (e^2*(n+2)^2+b^2*c^2*Log[F]^2)/(e^2*(n+1)*(n+2))*Int[F^(c*(a+b*x))*Cos[d+e*x]^(n+2),x] /;
FreeQ[{F,a,b,c,d,e},x] && NeQ[e^2*(n+2)^2+b^2*c^2*Log[F]^2] && RationalQ[n] && n<-1 && n!=-2


Int[F_^(c_.*(a_.+b_.*x_))*Sin[d_.+e_.*x_]^n_,x_Symbol] :=
  E^(I*n*(d+e*x))*Sin[d+e*x]^n/(-1+E^(2*I*(d+e*x)))^n*Int[F^(c*(a+b*x))*(-1+E^(2*I*(d+e*x)))^n/E^(I*n*(d+e*x)),x] /;
FreeQ[{F,a,b,c,d,e,n},x] && Not[IntegerQ[n]]


Int[F_^(c_.*(a_.+b_.*x_))*Cos[d_.+e_.*x_]^n_,x_Symbol] :=
  E^(I*n*(d+e*x))*Cos[d+e*x]^n/(1+E^(2*I*(d+e*x)))^n*Int[F^(c*(a+b*x))*(1+E^(2*I*(d+e*x)))^n/E^(I*n*(d+e*x)),x] /;
FreeQ[{F,a,b,c,d,e,n},x] && Not[IntegerQ[n]]


Int[F_^(c_.*(a_.+b_.*x_))*Tan[d_.+e_.*x_]^n_.,x_Symbol] :=
  I^n*Int[ExpandIntegrand[F^(c*(a+b*x))*(1-E^(2*I*(d+e*x)))^n/(1+E^(2*I*(d+e*x)))^n,x],x] /;
FreeQ[{F,a,b,c,d,e},x] && IntegerQ[n]


Int[F_^(c_.*(a_.+b_.*x_))*Cot[d_.+e_.*x_]^n_.,x_Symbol] :=
  (-I)^n*Int[ExpandIntegrand[F^(c*(a+b*x))*(1+E^(2*I*(d+e*x)))^n/(1-E^(2*I*(d+e*x)))^n,x],x] /;
FreeQ[{F,a,b,c,d,e},x] && IntegerQ[n]


Int[F_^(c_.*(a_.+b_.*x_))*Sec[d_.+e_.*x_]^n_,x_Symbol] :=
  b*c*Log[F]*F^(c*(a+b*x))*(Sec[d+e x]^n/(e^2*n^2+b^2*c^2*Log[F]^2)) - 
  e*n*F^(c*(a+b*x))*Sec[d+e x]^(n+1)*(Sin[d+e x]/(e^2*n^2+b^2*c^2*Log[F]^2)) + 
  e^2*n*((n+1)/(e^2*n^2+b^2*c^2*Log[F]^2))*Int[F^(c*(a+b*x))*Sec[d+e x]^(n+2),x] /;
FreeQ[{F,a,b,c,d,e},x] && NeQ[e^2*n^2+b^2*c^2*Log[F]^2] && RationalQ[n] && n<-1


Int[F_^(c_.*(a_.+b_.*x_))*Csc[d_.+e_.*x_]^n_,x_Symbol] :=
  b*c*Log[F]*F^(c*(a+b*x))*(Csc[d+e x]^n/(e^2*n^2+b^2*c^2*Log[F]^2)) + 
  e*n*F^(c*(a+b*x))*Csc[d+e x]^(n+1)*(Cos[d+e x]/(e^2*n^2+b^2*c^2*Log[F]^2)) + 
  e^2*n*((n+1)/(e^2*n^2+b^2*c^2*Log[F]^2))*Int[F^(c*(a+b*x))*Csc[d+e x]^(n+2),x] /;
FreeQ[{F,a,b,c,d,e},x] && NeQ[e^2*n^2+b^2*c^2*Log[F]^2] && RationalQ[n] && n<-1


Int[F_^(c_.*(a_.+b_.*x_))*Sec[d_.+e_.*x_]^n_,x_Symbol] :=
  -b*c*Log[F]*F^(c*(a+b*x))*Sec[d+e x]^(n-2)/(e^2*(n-1)*(n-2)) + 
  F^(c*(a+b*x))*Sec[d+e x]^(n-1)*Sin[d+e x]/(e*(n-1)) /;
FreeQ[{F,a,b,c,d,e,n},x] && EqQ[b^2*c^2*Log[F]^2+e^2*(n-2)^2] && NeQ[n-1] && NeQ[n-2]


Int[F_^(c_.*(a_.+b_.*x_))*Csc[d_.+e_.*x_]^n_,x_Symbol] :=
  -b*c*Log[F]*F^(c*(a+b*x))*Csc[d+e x]^(n-2)/(e^2*(n-1)*(n-2)) + 
  F^(c*(a+b*x))*Csc[d+e x]^(n-1)*Cos[d+e x]/(e*(n-1)) /;
FreeQ[{F,a,b,c,d,e,n},x] && EqQ[b^2*c^2*Log[F]^2+e^2*(n-2)^2] && NeQ[n-1] && NeQ[n-2]


Int[F_^(c_.*(a_.+b_.*x_))*Sec[d_.+e_.*x_]^n_,x_Symbol] :=
  -b*c*Log[F]*F^(c*(a+b*x))*Sec[d+e x]^(n-2)/(e^2*(n-1)*(n-2)) + 
  F^(c*(a+b*x))*Sec[d+e x]^(n-1)*Sin[d+e x]/(e*(n-1)) + 
  (e^2*(n-2)^2+b^2*c^2*Log[F]^2)/(e^2*(n-1)*(n-2))*Int[F^(c*(a+b*x))*Sec[d+e x]^(n-2),x] /;
FreeQ[{F,a,b,c,d,e},x] && NeQ[b^2*c^2*Log[F]^2+e^2*(n-2)^2] && RationalQ[n] && n>1 && n!=2


Int[F_^(c_.*(a_.+b_.*x_))*Csc[d_.+e_.*x_]^n_,x_Symbol] :=
  -b*c*Log[F]*F^(c*(a+b*x))*Csc[d+e x]^(n-2)/(e^2*(n-1)*(n-2)) - 
  F^(c*(a+b*x))*Csc[d+e x]^(n-1)*Cos[d+e x]/(e*(n-1)) + 
  (e^2*(n-2)^2+b^2*c^2*Log[F]^2)/(e^2*(n-1)*(n-2))*Int[F^(c*(a+b*x))*Csc[d+e x]^(n-2),x] /;
FreeQ[{F,a,b,c,d,e},x] && NeQ[b^2*c^2*Log[F]^2+e^2*(n-2)^2] && RationalQ[n] && n>1 && n!=2


(* Int[F_^(c_.*(a_.+b_.*x_))*Sec[d_.+e_.*x_]^n_.,x_Symbol] :=
  2^n*Int[SimplifyIntegrand[F^(c*(a+b*x))*E^(I*n*(d+e*x))/(1+E^(2*I*(d+e*x)))^n,x],x] /;
FreeQ[{F,a,b,c,d,e},x] && IntegerQ[n] *)


(* Int[F_^(c_.*(a_.+b_.*x_))*Csc[d_.+e_.*x_]^n_.,x_Symbol] :=
  (2*I)^n*Int[SimplifyIntegrand[F^(c*(a+b*x))*E^(-I*n*(d+e*x))/(1-E^(-2*I*(d+e*x)))^n,x],x] /;
FreeQ[{F,a,b,c,d,e},x] && IntegerQ[n] *)


Int[F_^(c_.*(a_.+b_.*x_))*Sec[d_.+k_.*Pi+e_.*x_]^n_.,x_Symbol] :=
  2^n*E^(I*k*n*Pi)*E^(I*n*(d+e*x))*F^(c*(a+b*x))/(I*e*n+b*c*Log[F])*
    Hypergeometric2F1[n,n/2-I*b*c*Log[F]/(2*e),1+n/2-I*b*c*Log[F]/(2*e),-E^(2*I*k*Pi)*E^(2*I*(d+e*x))] /;
FreeQ[{F,a,b,c,d,e},x] && IntegerQ[4*k] && IntegerQ[n]


Int[F_^(c_.*(a_.+b_.*x_))*Sec[d_.+e_.*x_]^n_.,x_Symbol] :=
  2^n*E^(I*n*(d+e*x))*F^(c*(a+b*x))/(I*e*n+b*c*Log[F])*
    Hypergeometric2F1[n,n/2-I*b*c*Log[F]/(2*e),1+n/2-I*b*c*Log[F]/(2*e),-E^(2*I*(d+e*x))] /;
FreeQ[{F,a,b,c,d,e},x] && IntegerQ[n]


Int[F_^(c_.*(a_.+b_.*x_))*Csc[d_.+k_.*Pi+e_.*x_]^n_.,x_Symbol] :=
  (-2*I)^n*E^(I*k*n*Pi)*E^(I*n*(d+e*x))*(F^(c*(a+b*x))/(I*e*n+b*c*Log[F]))*
    Hypergeometric2F1[n,n/2-I*b*c*Log[F]/(2*e),1+n/2-I*b*c*Log[F]/(2*e),E^(2*I*k*Pi)*E^(2*I*(d+e*x))] /;
FreeQ[{F,a,b,c,d,e},x] && IntegerQ[4*k] && IntegerQ[n]


Int[F_^(c_.*(a_.+b_.*x_))*Csc[d_.+e_.*x_]^n_.,x_Symbol] :=
  (-2*I)^n*E^(I*n*(d+e*x))*(F^(c*(a+b*x))/(I*e*n+b*c*Log[F]))*
    Hypergeometric2F1[n,n/2-I*b*c*Log[F]/(2*e),1+n/2-I*b*c*Log[F]/(2*e),E^(2*I*(d+e*x))] /;
FreeQ[{F,a,b,c,d,e},x] && IntegerQ[n]


Int[F_^(c_.*(a_.+b_.*x_))*Sec[d_.+e_.*x_]^n_.,x_Symbol] :=
  (1+E^(2*I*(d+e*x)))^n*Sec[d+e*x]^n/E^(I*n*(d+e*x))*Int[SimplifyIntegrand[F^(c*(a+b*x))*E^(I*n*(d+e*x))/(1+E^(2*I*(d+e*x)))^n,x],x] /;
FreeQ[{F,a,b,c,d,e},x] && Not[IntegerQ[n]]


Int[F_^(c_.*(a_.+b_.*x_))*Csc[d_.+e_.*x_]^n_.,x_Symbol] :=
  (1-E^(-2*I*(d+e*x)))^n*Csc[d+e*x]^n/E^(-I*n*(d+e*x))*Int[SimplifyIntegrand[F^(c*(a+b*x))*E^(-I*n*(d+e*x))/(1-E^(-2*I*(d+e*x)))^n,x],x] /;
FreeQ[{F,a,b,c,d,e},x] && Not[IntegerQ[n]]


Int[F_^(c_.*(a_.+b_.*x_))*(f_+g_.*Sin[d_.+e_.*x_])^n_.,x_Symbol] :=
  2^n*f^n*Int[F^(c*(a+b*x))*Cos[d/2+e*x/2-f*Pi/(4*g)]^(2*n),x] /;
FreeQ[{F,a,b,c,d,e,f,g},x] && EqQ[f^2-g^2] && NegativeIntegerQ[n]


Int[F_^(c_.*(a_.+b_.*x_))*(f_+g_.*Cos[d_.+e_.*x_])^n_.,x_Symbol] :=
  2^n*f^n*Int[F^(c*(a+b*x))*Cos[d/2+e*x/2]^(2*n),x] /;
FreeQ[{F,a,b,c,d,e,f,g},x] && EqQ[f-g] && NegativeIntegerQ[n]


Int[F_^(c_.*(a_.+b_.*x_))*(f_+g_.*Cos[d_.+e_.*x_])^n_.,x_Symbol] :=
  2^n*f^n*Int[F^(c*(a+b*x))*Sin[d/2+e*x/2]^(2*n),x] /;
FreeQ[{F,a,b,c,d,e,f,g},x] && EqQ[f+g] && NegativeIntegerQ[n]


Int[F_^(c_.*(a_.+b_.*x_))*Cos[d_.+e_.*x_]^m_.*(f_+g_.*Sin[d_.+e_.*x_])^n_.,x_Symbol] :=
  g^n*Int[F^(c*(a+b*x))*Tan[f*Pi/(4*g)-d/2-e*x/2]^m,x] /;
FreeQ[{F,a,b,c,d,e,f,g},x] && EqQ[f^2-g^2] && IntegersQ[m,n] && m+n==0


Int[F_^(c_.*(a_.+b_.*x_))*Sin[d_.+e_.*x_]^m_.*(f_+g_.*Cos[d_.+e_.*x_])^n_.,x_Symbol] :=
  f^n*Int[F^(c*(a+b*x))*Tan[d/2+e*x/2]^m,x] /;
FreeQ[{F,a,b,c,d,e,f,g},x] && EqQ[f-g] && IntegersQ[m,n] && m+n==0


Int[F_^(c_.*(a_.+b_.*x_))*Sin[d_.+e_.*x_]^m_.*(f_+g_.*Cos[d_.+e_.*x_])^n_.,x_Symbol] :=
  f^n*Int[F^(c*(a+b*x))*Cot[d/2+e*x/2]^m,x] /;
FreeQ[{F,a,b,c,d,e,f,g},x] && EqQ[f+g] && IntegersQ[m,n] && m+n==0


Int[F_^(c_.*(a_.+b_.*x_))*(h_+i_.*Cos[d_.+e_.*x_])/(f_+g_.*Sin[d_.+e_.*x_]),x_Symbol] :=
  2*i*Int[F^(c*(a+b*x))*(Cos[d+e*x]/(f+g*Sin[d+e*x])),x] + 
  Int[F^(c*(a+b*x))*((h-i*Cos[d+e*x])/(f+g*Sin[d+e*x])),x] /;
FreeQ[{F,a,b,c,d,e,f,g,h,i},x] && EqQ[f^2-g^2] && EqQ[h^2-i^2] && EqQ[g*h-f*i]


Int[F_^(c_.*(a_.+b_.*x_))*(h_+i_.*Sin[d_.+e_.*x_])/(f_+g_.*Cos[d_.+e_.*x_]),x_Symbol] :=
  2*i*Int[F^(c*(a+b*x))*(Sin[d+e*x]/(f+g*Cos[d+e*x])),x] + 
  Int[F^(c*(a+b*x))*((h-i*Sin[d+e*x])/(f+g*Cos[d+e*x])),x] /;
FreeQ[{F,a,b,c,d,e,f,g,h,i},x] && EqQ[f^2-g^2] && EqQ[h^2-i^2] && EqQ[g*h+f*i]


Int[F_^(c_.*u_)*G_[v_]^n_.,x_Symbol] :=
  Int[F^(c*ExpandToSum[u,x])*G[ExpandToSum[v,x]]^n,x] /;
FreeQ[{F,c,n},x] && TrigQ[G] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]


Int[(f_.*x_)^m_.*F_^(c_.*(a_.+b_.*x_))*Sin[d_.+e_.*x_]^n_.,x_Symbol] :=
  Module[{u=IntHide[F^(c*(a+b*x))*Sin[d+e*x]^n,x]},
  Dist[(f*x)^m,u,x] - f*m*Int[(f*x)^(m-1)*u,x]] /;
FreeQ[{F,a,b,c,d,e,f},x] && IGtQ[n,0] && GtQ[m,0]


Int[(f_.*x_)^m_.*F_^(c_.*(a_.+b_.*x_))*Cos[d_.+e_.*x_]^n_.,x_Symbol] :=
  Module[{u=IntHide[F^(c*(a+b*x))*Cos[d+e*x]^n,x]},
  Dist[(f*x)^m,u,x] - f*m*Int[(f*x)^(m-1)*u,x]] /;
FreeQ[{F,a,b,c,d,e,f},x] && IGtQ[n,0] && GtQ[m,0]


Int[(f_.*x_)^m_*F_^(c_.*(a_.+b_.*x_))*Sin[d_.+e_.*x_],x_Symbol] :=
  (f*x)^(m+1)/(f*(m+1))*F^(c*(a+b*x))*Sin[d+e*x] - 
  e/(f*(m+1))*Int[(f*x)^(m+1)*F^(c*(a+b*x))*Cos[d+e*x],x] - 
  b*c*Log[F]/(f*(m+1))*Int[(f*x)^(m+1)*F^(c*(a+b*x))*Sin[d+e*x],x] /;
FreeQ[{F,a,b,c,d,e,f,m},x] && (LtQ[m,-1] || SumSimplerQ[m,1])


Int[(f_.*x_)^m_*F_^(c_.*(a_.+b_.*x_))*Cos[d_.+e_.*x_],x_Symbol] :=
  (f*x)^(m+1)/(f*(m+1))*F^(c*(a+b*x))*Cos[d+e*x] + 
  e/(f*(m+1))*Int[(f*x)^(m+1)*F^(c*(a+b*x))*Sin[d+e*x],x] - 
  b*c*Log[F]/(f*(m+1))*Int[(f*x)^(m+1)*F^(c*(a+b*x))*Cos[d+e*x],x] /;
FreeQ[{F,a,b,c,d,e,f,m},x] && (LtQ[m,-1] || SumSimplerQ[m,1])


(* Int[(f_.*x_)^m_.*F_^(c_.*(a_.+b_.*x_))*Sin[d_.+e_.*x_]^n_.,x_Symbol] :=
  I^n/2^n*Int[ExpandIntegrand[(f*x)^m*F^(c*(a+b*x)),(E^(-I*(d+e*x))-E^(I*(d+e*x)))^n,x],x] /;
FreeQ[{F,a,b,c,d,e,f},x] && IGtQ[n,0] *)


(* Int[(f_.*x_)^m_.*F_^(c_.*(a_.+b_.*x_))*Cos[d_.+e_.*x_]^n_.,x_Symbol] :=
  1/2^n*Int[ExpandIntegrand[(f*x)^m*F^(c*(a+b*x)),(E^(-I*(d+e*x))+E^(I*(d+e*x)))^n,x],x] /;
FreeQ[{F,a,b,c,d,e,f},x] && IGtQ[n,0] *)


Int[F_^(c_.*(a_.+b_.*x_))*Sin[d_.+e_.*x_]^m_.*Cos[f_.+g_.*x_]^n_.,x_Symbol] :=
  Int[ExpandTrigReduce[F^(c*(a+b*x)),Sin[d+e*x]^m*Cos[f+g*x]^n,x],x] /;
FreeQ[{F,a,b,c,d,e,f,g},x] && PositiveIntegerQ[m,n]


Int[x_^p_.*F_^(c_.*(a_.+b_.*x_))*Sin[d_.+e_.*x_]^m_.*Cos[f_.+g_.*x_]^n_.,x_Symbol] :=
  Int[ExpandTrigReduce[x^p*F^(c*(a+b*x)),Sin[d+e*x]^m*Cos[f+g*x]^n,x],x] /;
FreeQ[{F,a,b,c,d,e,f,g},x] && PositiveIntegerQ[m,n,p]


Int[F_^(c_.*(a_.+b_.*x_))*G_[d_.+e_.*x_]^m_.*H_[d_.+e_.*x_]^n_.,x_Symbol] :=
  Int[ExpandTrigToExp[F^(c*(a+b*x)),G[d+e*x]^m*H[d+e*x]^n,x],x] /;
FreeQ[{F,a,b,c,d,e},x] && PositiveIntegerQ[m,n] && TrigQ[G] && TrigQ[H]


Int[F_^u_*Sin[v_]^n_.,x_Symbol] :=
  Int[ExpandTrigToExp[F^u,Sin[v]^n,x],x] /;
FreeQ[F,x] && (LinearQ[u,x] || PolyQ[u,x,2]) && (LinearQ[v,x] || PolyQ[v,x,2]) && PositiveIntegerQ[n]


Int[F_^u_*Cos[v_]^n_.,x_Symbol] :=
  Int[ExpandTrigToExp[F^u,Cos[v]^n,x],x] /;
FreeQ[F,x] && (LinearQ[u,x] || PolyQ[u,x,2]) && (LinearQ[v,x] || PolyQ[v,x,2]) && PositiveIntegerQ[n]


Int[F_^u_*Sin[v_]^m_.*Cos[v_]^n_.,x_Symbol] :=
  Int[ExpandTrigToExp[F^u,Sin[v]^m*Cos[v]^n,x],x] /;
FreeQ[F,x] && (LinearQ[u,x] || PolyQ[u,x,2]) && (LinearQ[v,x] || PolyQ[v,x,2]) && PositiveIntegerQ[m,n]





(* ::Subsection::Closed:: *)
(*4.4.7 x^m trig(a+b log(c x^n))^p*)


Int[Sin[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  x*(p+2)*Sin[a+b*Log[c*x^n]]^(p+2)/(p+1) + 
  x*Cot[a+b*Log[c*x^n]]*Sin[a+b*Log[c*x^n]]^(p+2)/(b*n*(p+1)) /;
FreeQ[{a,b,c,n,p},x] && EqQ[b^2*n^2*(p+2)^2+1] && NeQ[p+1]


Int[Cos[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  x*(p+2)*Cos[a+b*Log[c*x^n]]^(p+2)/(p+1) - 
  x*Tan[a+b*Log[c*x^n]]*Cos[a+b*Log[c*x^n]]^(p+2)/(b*n*(p+1)) /;
FreeQ[{a,b,c,n,p},x] && EqQ[b^2*n^2*(p+2)^2+1] && NeQ[p+1]


Int[Sin[a_.+b_.*Log[c_.*x_^n_.]]^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(E^(a*b*n*p)/(2*b*n*p)*(c*x^n)^(-1/(n*p))-E^(-a*b*n*p)/(2*b*n*p)*(c*x^n)^(1/(n*p)))^p,x],x] /;
FreeQ[{a,b,c,n},x] && PositiveIntegerQ[p] && EqQ[b^2*n^2*p^2+1]


Int[Cos[a_.+b_.*Log[c_.*x_^n_.]]^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(E^(a*b*n*p)/2*(c*x^n)^(-1/(n*p))-E^(-a*b*n*p)/2*(c*x^n)^(1/(n*p)))^p,x],x] /;
FreeQ[{a,b,c,n},x] && PositiveIntegerQ[p] && EqQ[b^2*n^2*p^2+1]


Int[Sin[a_.+b_.*Log[c_.*x_^n_.]],x_Symbol] :=
  x*Sin[a+b*Log[c*x^n]]/(b^2*n^2+1) -
  b*n*x*Cos[a+b*Log[c*x^n]]/(b^2*n^2+1) /;
FreeQ[{a,b,c,n},x] && NeQ[b^2*n^2+1]


Int[Cos[a_.+b_.*Log[c_.*x_^n_.]],x_Symbol] :=
  x*Cos[a+b*Log[c*x^n]]/(1+b^2*n^2) +
  b*n*x*Sin[a+b*Log[c*x^n]]/(b^2*n^2+1) /;
FreeQ[{a,b,c,n},x] && NeQ[b^2*n^2+1]


Int[Sin[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  x*Sin[a+b*Log[c*x^n]]^p/(b^2*n^2*p^2+1) -
  b*n*p*x*Cos[a+b*Log[c*x^n]]*Sin[a+b*Log[c*x^n]]^(p-1)/(b^2*n^2*p^2+1) +
  b^2*n^2*p*(p-1)/(b^2*n^2*p^2+1)*Int[Sin[a+b*Log[c*x^n]]^(p-2),x] /;
FreeQ[{a,b,c,n},x] && RationalQ[p] && p>1 && NeQ[b^2*n^2*p^2+1]


Int[Cos[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  x*Cos[a+b*Log[c*x^n]]^p/(b^2*n^2*p^2+1) +
  b*n*p*x*Cos[a+b*Log[c*x^n]]^(p-1)*Sin[a+b*Log[c*x^n]]/(b^2*n^2*p^2+1) +
  b^2*n^2*p*(p-1)/(b^2*n^2*p^2+1)*Int[Cos[a+b*Log[c*x^n]]^(p-2),x] /;
FreeQ[{a,b,c,n},x] && RationalQ[p] && p>1 && NeQ[b^2*n^2*p^2+1]


Int[Sin[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  x*Cot[a+b*Log[c*x^n]]*Sin[a+b*Log[c*x^n]]^(p+2)/(b*n*(p+1)) -
  x*Sin[a+b*Log[c*x^n]]^(p+2)/(b^2*n^2*(p+1)*(p+2)) +
  (b^2*n^2*(p+2)^2+1)/(b^2*n^2*(p+1)*(p+2))*Int[Sin[a+b*Log[c*x^n]]^(p+2),x] /;
FreeQ[{a,b,c,n},x] && RationalQ[p] && p<-1 && p!=-2 && NeQ[b^2*n^2*(p+2)^2+1]


Int[Cos[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  -x*Tan[a+b*Log[c*x^n]]*Cos[a+b*Log[c*x^n]]^(p+2)/(b*n*(p+1)) -
  x*Cos[a+b*Log[c*x^n]]^(p+2)/(b^2*n^2*(p+1)*(p+2)) +
  (b^2*n^2*(p+2)^2+1)/(b^2*n^2*(p+1)*(p+2))*Int[Cos[a+b*Log[c*x^n]]^(p+2),x] /;
FreeQ[{a,b,c,n},x] && RationalQ[p] && p<-1 && p!=-2 && NeQ[b^2*n^2*(p+2)^2+1]


Int[Sin[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  x*(I/(E^(I*a)*(c*x^n)^(I*b))-I*E^(I*a)*(c*x^n)^(I*b))^p/((1-I*b*n*p)*(2-2*E^(2*I*a)*(c*x^n)^(2*I*b))^p)*
    Hypergeometric2F1[-p,(1-I*b*n*p)/(2*I*b*n),1+(1-I*b*n*p)/(2*I*b*n),E^(2*I*a)*(c*x^n)^(2*I*b)] /;
FreeQ[{a,b,c,n,p},x] && NeQ[b^2*n^2*p^2+1]


Int[Cos[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  x*(1/(E^(I*a)*(c*x^n)^(I*b))+E^(I*a)*(c*x^n)^(I*b))^p/((1-I*b*n*p)*(2+2*E^(2*I*a)*(c*x^n)^(2*I*b))^p)*
    Hypergeometric2F1[-p,(1-I*b*n*p)/(2*I*b*n),1+(1-I*b*n*p)/(2*I*b*n),-E^(2*I*a)*(c*x^n)^(2*I*b)] /;
FreeQ[{a,b,c,n,p},x] && NeQ[b^2*n^2*p^2+1]


Int[x_^m_.*Sin[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  (p+2)*x^(m+1)*Sin[a+b*Log[c*x^n]]^(p+2)/((m+1)*(p+1)) + 
  x^(m+1)*Cot[a+b*Log[c*x^n]]*Sin[a+b*Log[c*x^n]]^(p+2)/(b*n*(p+1)) /;
FreeQ[{a,b,c,m,n,p},x] && EqQ[b^2*n^2*(p+2)^2+(m+1)^2] && NeQ[p+1] && NeQ[m+1]


Int[x_^m_.*Cos[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  (p+2)*x^(m+1)*Cos[a+b*Log[c*x^n]]^(p+2)/((m+1)*(p+1)) - 
  x^(m+1)*Tan[a+b*Log[c*x^n]]*Cos[a+b*Log[c*x^n]]^(p+2)/(b*n*(p+1)) /;
FreeQ[{a,b,c,m,n,p},x] && EqQ[b^2*n^2*(p+2)^2+(m+1)^2] && NeQ[p+1] && NeQ[m+1]


Int[x_^m_.*Sin[a_.+b_.*Log[c_.*x_^n_.]]^p_.,x_Symbol] :=
  1/2^p*Int[ExpandIntegrand[x^m*((m+1)/(b*n*p)*E^(a*b*n*p/(m+1))*(c*x^n)^(-(m+1)/(n*p)) - 
    (m+1)/(b*n*p)*E^(-a*b*n*p/(m+1))*(c*x^n)^((m+1)/(n*p)))^p,x],x] /;
FreeQ[{a,b,c,m,n},x] && PositiveIntegerQ[p] && EqQ[b^2*n^2*p^2+(m+1)^2]


Int[x_^m_.*Cos[a_.+b_.*Log[c_.*x_^n_.]]^p_.,x_Symbol] :=
  1/2^p*Int[ExpandIntegrand[x^m*(E^(a*b*n*p/(m+1))*(c*x^n)^(-(m+1)/(n*p)) - 
    E^(-a*b*n*p/(m+1))*(c*x^n)^((m+1)/(n*p)))^p,x],x] /;
FreeQ[{a,b,c,m,n},x] && PositiveIntegerQ[p] && EqQ[b^2*n^2*p^2+(m+1)^2]


Int[x_^m_.*Sin[a_.+b_.*Log[c_.*x_^n_.]],x_Symbol] :=
  (m+1)*x^(m+1)*Sin[a+b*Log[c*x^n]]/(b^2*n^2+(m+1)^2) -
  b*n*x^(m+1)*Cos[a+b*Log[c*x^n]]/(b^2*n^2+(m+1)^2) /;
FreeQ[{a,b,c,m,n},x] && NeQ[b^2*n^2+(m+1)^2]


Int[x_^m_.*Cos[a_.+b_.*Log[c_.*x_^n_.]],x_Symbol] :=
  (m+1)*x^(m+1)*Cos[a+b*Log[c*x^n]]/(b^2*n^2+(m+1)^2) +
  b*n*x^(m+1)*Sin[a+b*Log[c*x^n]]/(b^2*n^2+(m+1)^2) /;
FreeQ[{a,b,c,m,n},x] && NeQ[b^2*n^2+(m+1)^2]


Int[x_^m_.*Sin[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  (m+1)*x^(m+1)*Sin[a+b*Log[c*x^n]]^p/(b^2*n^2*p^2+(m+1)^2) -
  b*n*p*x^(m+1)*Cos[a+b*Log[c*x^n]]*Sin[a+b*Log[c*x^n]]^(p-1)/(b^2*n^2*p^2+(m+1)^2) +
  b^2*n^2*p*(p-1)/(b^2*n^2*p^2+(m+1)^2)*Int[x^m*Sin[a+b*Log[c*x^n]]^(p-2),x] /;
FreeQ[{a,b,c,m,n},x] && RationalQ[p] && p>1 && NeQ[b^2*n^2*p^2+(m+1)^2]


Int[x_^m_.*Cos[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  (m+1)*x^(m+1)*Cos[a+b*Log[c*x^n]]^p/(b^2*n^2*p^2+(m+1)^2) +
  b*n*p*x^(m+1)*Sin[a+b*Log[c*x^n]]*Cos[a+b*Log[c*x^n]]^(p-1)/(b^2*n^2*p^2+(m+1)^2) +
  b^2*n^2*p*(p-1)/(b^2*n^2*p^2+(m+1)^2)*Int[x^m*Cos[a+b*Log[c*x^n]]^(p-2),x] /;
FreeQ[{a,b,c,m,n},x] && RationalQ[p] && p>1 && NeQ[b^2*n^2*p^2+(m+1)^2]


Int[x_^m_.*Sin[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  x^(m+1)*Cot[a+b*Log[c*x^n]]*Sin[a+b*Log[c*x^n]]^(p+2)/(b*n*(p+1)) -
  (m+1)*x^(m+1)*Sin[a+b*Log[c*x^n]]^(p+2)/(b^2*n^2*(p+1)*(p+2)) +
  (b^2*n^2*(p+2)^2+(m+1)^2)/(b^2*n^2*(p+1)*(p+2))*Int[x^m*Sin[a+b*Log[c*x^n]]^(p+2),x] /;
FreeQ[{a,b,c,m,n},x] && RationalQ[p] && p<-1 && p!=-2 && NeQ[b^2*n^2*(p+2)^2+(m+1)^2]


Int[x_^m_.*Cos[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  -x^(m+1)*Tan[a+b*Log[c*x^n]]*Cos[a+b*Log[c*x^n]]^(p+2)/(b*n*(p+1)) -
  (m+1)*x^(m+1)*Cos[a+b*Log[c*x^n]]^(p+2)/(b^2*n^2*(p+1)*(p+2)) +
  (b^2*n^2*(p+2)^2+(m+1)^2)/(b^2*n^2*(p+1)*(p+2))*Int[x^m*Cos[a+b*Log[c*x^n]]^(p+2),x] /;
FreeQ[{a,b,c,m,n},x] && RationalQ[p] && p<-1 && p!=-2 && NeQ[b^2*n^2*(p+2)^2+(m+1)^2]


Int[x_^m_.*Sin[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  x^(m+1)*(I*E^(-I*a)*(c*x^n)^(-I*b)-I*E^(I*a)*(c*x^n)^(I*b))^p/((m+1-I*b*n*p)*(2-2*E^(2*I*a)*(c*x^n)^(2*I*b))^p)*
    Hypergeometric2F1[-p,(m+1-I*b*n*p)/(2*I*b*n),1+(m+1-I*b*n*p)/(2*I*b*n),E^(2*I*a)*(c*x^n)^(2*I*b)] /;
FreeQ[{a,b,c,m,n,p},x] && NeQ[b^2*n^2*p^2+(m+1)^2]


Int[x_^m_.*Cos[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  x^(m+1)*(E^(-I*a)*(c*x^n)^(-I*b)+E^(I*a)*(c*x^n)^(I*b))^p/((m+1-I*b*n*p)*(2+2*E^(2*I*a)*(c*x^n)^(2*I*b))^p)*
    Hypergeometric2F1[-p,(m+1-I*b*n*p)/(2*I*b*n),1+(m+1-I*b*n*p)/(2*I*b*n),-E^(2*I*a)*(c*x^n)^(2*I*b)] /;
FreeQ[{a,b,c,m,n,p},x] && NeQ[b^2*n^2*p^2+(m+1)^2]


Int[Sec[a_.+b_.*Log[c_.*x_^n_.]],x_Symbol] :=
  2*E^(a*b*n)*Int[(c*x^n)^(1/n)/(E^(2*a*b*n)+(c*x^n)^(2/n)),x] /;
FreeQ[{a,b,c,n},x] && EqQ[b^2*n^2+1]


Int[Csc[a_.+b_.*Log[c_.*x_^n_.]],x_Symbol] :=
  2*b*n*E^(a*b*n)*Int[(c*x^n)^(1/n)/(E^(2*a*b*n)-(c*x^n)^(2/n)),x] /;
FreeQ[{a,b,c,n},x] && EqQ[b^2*n^2+1]


Int[Sec[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  (p-2)*x*Sec[a+b*Log[c*x^n]]^(p-2)/(p-1) + 
  x*Tan[a+b*Log[c*x^n]]*Sec[a+b*Log[c*x^n]]^(p-2)/(b*n*(p-1)) /;
FreeQ[{a,b,c,n,p},x] && EqQ[b^2*n^2*(p-2)^2+1] && NeQ[p-1]


Int[Csc[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  (p-2)*x*Csc[a+b*Log[c*x^n]]^(p-2)/(p-1) - 
  x*Cot[a+b*Log[c*x^n]]*Csc[a+b*Log[c*x^n]]^(p-2)/(b*n*(p-1)) /;
FreeQ[{a,b,c,n,p},x] && EqQ[b^2*n^2*(p-2)^2+1] && NeQ[p-1]


Int[Sec[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  x*Tan[a+b*Log[c*x^n]]*Sec[a+b*Log[c*x^n]]^(p-2)/(b*n*(p-1)) -
  x*Sec[a+b*Log[c*x^n]]^(p-2)/(b^2*n^2*(p-1)*(p-2)) +
  (b^2*n^2*(p-2)^2+1)/(b^2*n^2*(p-1)*(p-2))*Int[Sec[a+b*Log[c*x^n]]^(p-2),x] /;
FreeQ[{a,b,c,n},x] && RationalQ[p] && p>1 && p!=2 && NeQ[b^2*n^2*(p-2)^2+1]


Int[Csc[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  -x*Cot[a+b*Log[c*x^n]]*Csc[a+b*Log[c*x^n]]^(p-2)/(b*n*(p-1)) -
  x*Csc[a+b*Log[c*x^n]]^(p-2)/(b^2*n^2*(p-1)*(p-2)) +
  (b^2*n^2*(p-2)^2+1)/(b^2*n^2*(p-1)*(p-2))*Int[Csc[a+b*Log[c*x^n]]^(p-2),x] /;
FreeQ[{a,b,c,n},x] && RationalQ[p] && p>1 && p!=2 && NeQ[b^2*n^2*(p-2)^2+1]


Int[Sec[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  -b*n*p*x*Sin[a+b*Log[c*x^n]]*Sec[a+b*Log[c*x^n]]^(p+1)/(b^2*n^2*p^2+1) +
  x*Sec[a+b*Log[c*x^n]]^p/(b^2*n^2*p^2+1) +
  b^2*n^2*p*(p+1)/(b^2*n^2*p^2+1)*Int[Sec[a+b*Log[c*x^n]]^(p+2),x] /;
FreeQ[{a,b,c,n},x] && RationalQ[p] && p<-1 && NeQ[b^2*n^2*p^2+1]


Int[Csc[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  b*n*p*x*Cos[a+b*Log[c*x^n]]*Csc[a+b*Log[c*x^n]]^(p+1)/(b^2*n^2*p^2+1) +
  x*Csc[a+b*Log[c*x^n]]^p/(b^2*n^2*p^2+1) +
  b^2*n^2*p*(p+1)/(b^2*n^2*p^2+1)*Int[Csc[a+b*Log[c*x^n]]^(p+2),x] /;
FreeQ[{a,b,c,n},x] && RationalQ[p] && p<-1 && NeQ[b^2*n^2*p^2+1]


Int[Sec[a_.+b_.*Log[c_.*x_^n_.]]^p_.,x_Symbol] :=
  x*(2+2*E^(2*I*a)*(c*x^n)^(2*I*b))^p/(1+I*b*n*p)*
    (E^(I*a)*(c*x^n)^(I*b)/(1+E^(2*I*a)*(c*x^n)^(2*I*b)))^p*
    Hypergeometric2F1[p,(1+I*b*n*p)/(2*I*b*n),1+(1+I*b*n*p)/(2*I*b*n),-E^(2*I*a)*(c*x^n)^(2*I*b)] /;
FreeQ[{a,b,c,n,p},x] && NeQ[b^2*n^2*p^2+1]


Int[Csc[a_.+b_.*Log[c_.*x_^n_.]]^p_.,x_Symbol] :=
  x*(2-2*E^(2*I*a)*(c*x^n)^(2*I*b))^p/(1+I*b*n*p)*
    (-I*E^(I*a)*(c*x^n)^(I*b)/(1-E^(2*I*a)*(c*x^n)^(2*I*b)))^p*
    Hypergeometric2F1[p,(1+I*b*n*p)/(2*I*b*n),1+(1+I*b*n*p)/(2*I*b*n),E^(2*I*a)*(c*x^n)^(2*I*b)] /;
FreeQ[{a,b,c,n,p},x] && NeQ[b^2*n^2*p^2+1]


Int[x_^m_.*Sec[a_.+b_.*Log[c_.*x_^n_.]],x_Symbol] :=
  2*E^(a*b*n/(m+1))*Int[x^m*(c*x^n)^((m+1)/n)/(E^(2*a*b*n/(m+1))+(c*x^n)^(2*(m+1)/n)),x] /;
FreeQ[{a,b,c,m,n},x] && EqQ[b^2*n^2+(m+1)^2]


Int[x_^m_.*Csc[a_.+b_.*Log[c_.*x_^n_.]],x_Symbol] :=
  2*b*n/(m+1)*E^(a*b*n/(m+1))*Int[x^m*(c*x^n)^((m+1)/n)/(E^(2*a*b*n/(m+1))-(c*x^n)^(2*(m+1)/n)),x] /;
FreeQ[{a,b,c,m,n},x] && EqQ[b^2*n^2+(m+1)^2]


Int[x_^m_.*Sec[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  (p-2)*x^(m+1)*Sec[a+b*Log[c*x^n]]^(p-2)/((m+1)*(p-1)) + 
  x^(m+1)*Tan[a+b*Log[c*x^n]]*Sec[a+b*Log[c*x^n]]^(p-2)/(b*n*(p-1)) /;
FreeQ[{a,b,c,m,n,p},x] && EqQ[b^2*n^2*(p-2)^2+(m+1)^2] && NeQ[m+1] && NeQ[p-1]


Int[x_^m_.*Csc[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  (p-2)*x^(m+1)*Csc[a+b*Log[c*x^n]]^(p-2)/((m+1)*(p-1)) - 
  x^(m+1)*Cot[a+b*Log[c*x^n]]*Csc[a+b*Log[c*x^n]]^(p-2)/(b*n*(p-1)) /;
FreeQ[{a,b,c,m,n,p},x] && EqQ[b^2*n^2*(p-2)^2+(m+1)^2] && NeQ[m+1] && NeQ[p-1]


Int[x_^m_.*Sec[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  x^(m+1)*Tan[a+b*Log[c*x^n]]*Sec[a+b*Log[c*x^n]]^(p-2)/(b*n*(p-1)) -
  (m+1)*x^(m+1)*Sec[a+b*Log[c*x^n]]^(p-2)/(b^2*n^2*(p-1)*(p-2)) +
  (b^2*n^2*(p-2)^2+(m+1)^2)/(b^2*n^2*(p-1)*(p-2))*Int[x^m*Sec[a+b*Log[c*x^n]]^(p-2),x] /;
FreeQ[{a,b,c,m,n},x] && RationalQ[p] && p>1 && p!=2 && NeQ[b^2*n^2*(p-2)^2+(m+1)^2]


Int[x_^m_.*Csc[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  -x^(m+1)*Cot[a+b*Log[c*x^n]]*Csc[a+b*Log[c*x^n]]^(p-2)/(b*n*(p-1)) -
  (m+1)*x^(m+1)*Csc[a+b*Log[c*x^n]]^(p-2)/(b^2*n^2*(p-1)*(p-2)) +
  (b^2*n^2*(p-2)^2+(m+1)^2)/(b^2*n^2*(p-1)*(p-2))*Int[x^m*Csc[a+b*Log[c*x^n]]^(p-2),x] /;
FreeQ[{a,b,c,m,n},x] && RationalQ[p] && p>1 && p!=2 && NeQ[b^2*n^2*(p-2)^2+(m+1)^2]


Int[x_^m_.*Sec[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  -b*n*p*x^(m+1)*Sin[a+b*Log[c*x^n]]*Sec[a+b*Log[c*x^n]]^(p+1)/(b^2*n^2*p^2+(m+1)^2) +
  (m+1)*x^(m+1)*Sec[a+b*Log[c*x^n]]^p/(b^2*n^2*p^2+(m+1)^2) +
  b^2*n^2*p*(p+1)/(b^2*n^2*p^2+(m+1)^2)*Int[x^m*Sec[a+b*Log[c*x^n]]^(p+2),x] /;
FreeQ[{a,b,c,m,n},x] && RationalQ[p] && p<-1 && NeQ[b^2*n^2*p^2+(m+1)^2]


Int[x_^m_.*Csc[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
  b*n*p*x^(m+1)*Cos[a+b*Log[c*x^n]]*Csc[a+b*Log[c*x^n]]^(p+1)/(b^2*n^2*p^2+(m+1)^2) +
  (m+1)*x^(m+1)*Csc[a+b*Log[c*x^n]]^p/(b^2*n^2*p^2+(m+1)^2) +
  b^2*n^2*p*(p+1)/(b^2*n^2*p^2+(m+1)^2)*Int[x^m*Csc[a+b*Log[c*x^n]]^(p+2),x] /;
FreeQ[{a,b,c,m,n},x] && RationalQ[p] && p<-1 && NeQ[b^2*n^2*p^2+(m+1)^2]


Int[x_^m_.*Sec[a_.+b_.*Log[c_.*x_^n_.]]^p_.,x_Symbol] :=
  x^(m+1)*(2+2*E^(2*I*a)*(c*x^n)^(2*I*b))^p/(m+1+I*b*n*p)*
    (E^(I*a)*(c*x^n)^(I*b)/(1+E^(2*I*a)*(c*x^n)^(2*I*b)))^p*
    Hypergeometric2F1[p,(m+1+I*b*n*p)/(2*I*b*n),1+(m+1+I*b*n*p)/(2*I*b*n),-E^(2*I*a)*(c*x^n)^(2*I*b)] /;
FreeQ[{a,b,c,m,n,p},x] && NeQ[b^2*n^2*p^2+(m+1)^2]


Int[x_^m_.*Csc[a_.+b_.*Log[c_.*x_^n_.]]^p_.,x_Symbol] :=
  x^(m+1)*(2-2*E^(2*I*a)*(c*x^n)^(2*I*b))^p/(m+1+I*b*n*p)*
    (-I*E^(I*a)*(c*x^n)^(I*b)/(1-E^(2*I*a)*(c*x^n)^(2*I*b)))^p*
    Hypergeometric2F1[p,(m+1+I*b*n*p)/(2*I*b*n),1+(m+1+I*b*n*p)/(2*I*b*n),E^(2*I*a)*(c*x^n)^(2*I*b)] /;
FreeQ[{a,b,c,m,n,p},x] && NeQ[b^2*n^2*p^2+(m+1)^2]


Int[Sin[a_.*x_*Log[b_.*x_]^p_.]*Log[b_.*x_]^p_.,x_Symbol] :=
  -Cos[a*x*Log[b*x]^p]/a -
  p*Int[Sin[a*x*Log[b*x]^p]*Log[b*x]^(p-1),x] /;
FreeQ[{a,b},x] && RationalQ[p] && p>0


Int[Cos[a_.*x_*Log[b_.*x_]^p_.]*Log[b_.*x_]^p_.,x_Symbol] :=
  Sin[a*x*Log[b*x]^p]/a -
  p*Int[Cos[a*x*Log[b*x]^p]*Log[b*x]^(p-1),x] /;
FreeQ[{a,b},x] && RationalQ[p] && p>0


Int[Sin[a_.*x_^n_*Log[b_.*x_]^p_.]*Log[b_.*x_]^p_.,x_Symbol] :=
  -Cos[a*x^n*Log[b*x]^p]/(a*n*x^(n-1)) -
  p/n*Int[Sin[a*x^n*Log[b*x]^p]*Log[b*x]^(p-1),x] -
  (n-1)/(a*n)*Int[Cos[a*x^n*Log[b*x]^p]/x^n,x] /;
FreeQ[{a,b},x] && RationalQ[n,p] && p>0


Int[Cos[a_.*x_^n_*Log[b_.*x_]^p_.]*Log[b_.*x_]^p_.,x_Symbol] :=
  Sin[a*x^n*Log[b*x]^p]/(a*n*x^(n-1)) -
  p/n*Int[Cos[a*x^n*Log[b*x]^p]*Log[b*x]^(p-1),x] +
  (n-1)/(a*n)*Int[Sin[a*x^n*Log[b*x]^p]/x^n,x] /;
FreeQ[{a,b},x] && RationalQ[n,p] && p>0


Int[x_^m_.*Sin[a_.*x_^n_.*Log[b_.*x_]^p_.]*Log[b_.*x_]^p_.,x_Symbol] :=
  -Cos[a*x^n*Log[b*x]^p]/(a*n) -
  p/n*Int[x^m*Sin[a*x^n*Log[b*x]^p]*Log[b*x]^(p-1),x] /;
FreeQ[{a,b,m,n},x] && EqQ[m-n+1] && RationalQ[p] && p>0


Int[x_^m_.*Cos[a_.*x_^n_.*Log[b_.*x_]^p_.]*Log[b_.*x_]^p_.,x_Symbol] :=
  Sin[a*x^n*Log[b*x]^p]/(a*n) -
  p/n*Int[x^m*Cos[a*x^n*Log[b*x]^p]*Log[b*x]^(p-1),x] /;
FreeQ[{a,b,m,n},x] && EqQ[m-n+1] && RationalQ[p] && p>0


Int[x_^m_.*Sin[a_.*x_^n_.*Log[b_.*x_]^p_.]*Log[b_.*x_]^p_.,x_Symbol] :=
  -x^(m-n+1)*Cos[a*x^n*Log[b*x]^p]/(a*n) -
  p/n*Int[x^m*Sin[a*x^n*Log[b*x]^p]*Log[b*x]^(p-1),x] +
  (m-n+1)/(a*n)*Int[x^(m-n)*Cos[a*x^n*Log[b*x]^p],x] /;
FreeQ[{a,b,m,n},x] && RationalQ[p] && p>0 && NeQ[m-n+1]


Int[x_^m_*Cos[a_.*x_^n_.*Log[b_.*x_]^p_.]*Log[b_.*x_]^p_.,x_Symbol] :=
  x^(m-n+1)*Sin[a*x^n*Log[b*x]^p]/(a*n) -
  p/n*Int[x^m*Cos[a*x^n*Log[b*x]^p]*Log[b*x]^(p-1),x] -
  (m-n+1)/(a*n)*Int[x^(m-n)*Sin[a*x^n*Log[b*x]^p],x] /;
FreeQ[{a,b,m,n},x] && RationalQ[p] && p>0 && NeQ[m-n+1]





(* ::Subsection::Closed:: *)
(*4.4.8 Active trig functions*)


Int[Sin[a_./(c_.+d_.*x_)]^n_.,x_Symbol] :=
  -1/d*Subst[Int[Sin[a*x]^n/x^2,x],x,1/(c+d*x)] /;
FreeQ[{a,c,d},x] && PositiveIntegerQ[n]


Int[Cos[a_./(c_.+d_.*x_)]^n_.,x_Symbol] :=
  -1/d*Subst[Int[Cos[a*x]^n/x^2,x],x,1/(c+d*x)] /;
FreeQ[{a,c,d},x] && PositiveIntegerQ[n]


Int[Sin[e_.*(a_.+b_.*x_)/(c_.+d_.*x_)]^n_.,x_Symbol] :=
  -1/d*Subst[Int[Sin[b*e/d-e*(b*c-a*d)*x/d]^n/x^2,x],x,1/(c+d*x)] /;
FreeQ[{a,b,c,d},x] && PositiveIntegerQ[n] && NeQ[b*c-a*d]


Int[Cos[e_.*(a_.+b_.*x_)/(c_.+d_.*x_)]^n_.,x_Symbol] :=
  -1/d*Subst[Int[Cos[b*e/d-e*(b*c-a*d)*x/d]^n/x^2,x],x,1/(c+d*x)] /;
FreeQ[{a,b,c,d},x] && PositiveIntegerQ[n] && NeQ[b*c-a*d]


Int[Sin[u_]^n_.,x_Symbol] :=
  Module[{lst=QuotientOfLinearsParts[u,x]},
  Int[Sin[(lst[[1]]+lst[[2]]*x)/(lst[[3]]+lst[[4]]*x)]^n,x]] /;
PositiveIntegerQ[n] && QuotientOfLinearsQ[u,x]


Int[Cos[u_]^n_.,x_Symbol] :=
  Module[{lst=QuotientOfLinearsParts[u,x]},
  Int[Cos[(lst[[1]]+lst[[2]]*x)/(lst[[3]]+lst[[4]]*x)]^n,x]] /;
PositiveIntegerQ[n] && QuotientOfLinearsQ[u,x]


Int[u_.*Sin[v_]^p_.*Sin[w_]^q_.,x_Symbol] :=
  Int[u*Sin[v]^(p+q),x] /;
EqQ[v-w]


Int[u_.*Cos[v_]^p_.*Cos[w_]^q_.,x_Symbol] :=
  Int[u*Cos[v]^(p+q),x] /;
EqQ[v-w]


Int[Sin[v_]^p_.*Sin[w_]^q_.,x_Symbol] :=
  Int[ExpandTrigReduce[Sin[v]^p*Sin[w]^q,x],x] /;
(PolynomialQ[v,x] && PolynomialQ[w,x] || BinomialQ[{v,w},x] && IndependentQ[Cancel[v/w],x]) && PositiveIntegerQ[p,q]


Int[Cos[v_]^p_.*Cos[w_]^q_.,x_Symbol] :=
  Int[ExpandTrigReduce[Cos[v]^p*Cos[w]^q,x],x] /;
(PolynomialQ[v,x] && PolynomialQ[w,x] || BinomialQ[{v,w},x] && IndependentQ[Cancel[v/w],x]) && PositiveIntegerQ[p,q]


Int[x_^m_.*Sin[v_]^p_.*Sin[w_]^q_.,x_Symbol] :=
  Int[ExpandTrigReduce[x^m,Sin[v]^p*Sin[w]^q,x],x] /;
PositiveIntegerQ[m,p,q] && (PolynomialQ[v,x] && PolynomialQ[w,x] || BinomialQ[{v,w},x] && IndependentQ[Cancel[v/w],x])


Int[x_^m_.*Cos[v_]^p_.*Cos[w_]^q_.,x_Symbol] :=
  Int[ExpandTrigReduce[x^m,Cos[v]^p*Cos[w]^q,x],x] /;
PositiveIntegerQ[m,p,q] && (PolynomialQ[v,x] && PolynomialQ[w,x] || BinomialQ[{v,w},x] && IndependentQ[Cancel[v/w],x])


Int[u_.*Sin[v_]^p_.*Cos[w_]^p_.,x_Symbol] :=
  1/2^p*Int[u*Sin[2*v]^p,x] /;
EqQ[v-w] && IntegerQ[p]


Int[Sin[v_]^p_.*Cos[w_]^q_.,x_Symbol] :=
  Int[ExpandTrigReduce[Sin[v]^p*Cos[w]^q,x],x] /;
PositiveIntegerQ[p,q] && (PolynomialQ[v,x] && PolynomialQ[w,x] || BinomialQ[{v,w},x] && IndependentQ[Cancel[v/w],x])


Int[x_^m_.*Sin[v_]^p_.*Cos[w_]^q_.,x_Symbol] :=
  Int[ExpandTrigReduce[x^m,Sin[v]^p*Cos[w]^q,x],x] /;
PositiveIntegerQ[m,p,q] && (PolynomialQ[v,x] && PolynomialQ[w,x] || BinomialQ[{v,w},x] && IndependentQ[Cancel[v/w],x])


Int[Sin[v_]*Tan[w_]^n_.,x_Symbol] :=
  -Int[Cos[v]*Tan[w]^(n-1),x] + Cos[v-w]*Int[Sec[w]*Tan[w]^(n-1),x] /;
RationalQ[n] && n>0 && FreeQ[v-w,x] && NeQ[v-w]


Int[Cos[v_]*Cot[w_]^n_.,x_Symbol] :=
  -Int[Sin[v]*Cot[w]^(n-1),x] + Cos[v-w]*Int[Csc[w]*Cot[w]^(n-1),x] /;
RationalQ[n] && n>0 && FreeQ[v-w,x] && NeQ[v-w]


Int[Sin[v_]*Cot[w_]^n_.,x_Symbol] :=
  Int[Cos[v]*Cot[w]^(n-1),x] + Sin[v-w]*Int[Csc[w]*Cot[w]^(n-1),x] /;
RationalQ[n] && n>0 && FreeQ[v-w,x] && NeQ[v-w]


Int[Cos[v_]*Tan[w_]^n_.,x_Symbol] :=
  Int[Sin[v]*Tan[w]^(n-1),x] - Sin[v-w]*Int[Sec[w]*Tan[w]^(n-1),x] /;
RationalQ[n] && n>0 && FreeQ[v-w,x] && NeQ[v-w]


Int[Sin[v_]*Sec[w_]^n_.,x_Symbol] :=
  Cos[v-w]*Int[Tan[w]*Sec[w]^(n-1),x] + Sin[v-w]*Int[Sec[w]^(n-1),x] /;
RationalQ[n] && n>0 && FreeQ[v-w,x] && NeQ[v-w]


Int[Cos[v_]*Csc[w_]^n_.,x_Symbol] :=
  Cos[v-w]*Int[Cot[w]*Csc[w]^(n-1),x] - Sin[v-w]*Int[Csc[w]^(n-1),x] /;
RationalQ[n] && n>0 && FreeQ[v-w,x] && NeQ[v-w]


Int[Sin[v_]*Csc[w_]^n_.,x_Symbol] :=
  Sin[v-w]*Int[Cot[w]*Csc[w]^(n-1),x] + Cos[v-w]*Int[Csc[w]^(n-1),x] /;
RationalQ[n] && n>0 && FreeQ[v-w,x] && NeQ[v-w]


Int[Cos[v_]*Sec[w_]^n_.,x_Symbol] :=
  -Sin[v-w]*Int[Tan[w]*Sec[w]^(n-1),x] + Cos[v-w]*Int[Sec[w]^(n-1),x] /;
RationalQ[n] && n>0 && FreeQ[v-w,x] && NeQ[v-w]


Int[(e_.+f_.*x_)^m_.*(a_+b_.*Sin[c_.+d_.*x_]*Cos[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[(e+f*x)^m*(a+b*Sin[2*c+2*d*x]/2)^n,x] /;
FreeQ[{a,b,c,d,e,f,m,n},x]


Int[x_^m_.*(a_+b_.*Sin[c_.+d_.*x_]^2)^n_,x_Symbol] :=
  1/2^n*Int[x^m*(2*a+b-b*Cos[2*c+2*d*x])^n,x] /;
FreeQ[{a,b,c,d},x] && NeQ[a+b] && IntegersQ[m,n] && m>0 && n<0 && (n==-1 || m==1 && n==-2)


Int[x_^m_.*(a_+b_.*Cos[c_.+d_.*x_]^2)^n_,x_Symbol] :=
  1/2^n*Int[x^m*(2*a+b+b*Cos[2*c+2*d*x])^n,x] /;
FreeQ[{a,b,c,d},x] && NeQ[a+b] && IntegersQ[m,n] && m>0 && n<0 && (n==-1 || m==1 && n==-2)


Int[(e_.+f_.*x_)^m_.*Sin[a_.+b_.*(c_+d_.*x_)^n_]^p_.,x_Symbol] :=
  1/d^(m+1)*Subst[Int[(d*e-c*f+f*x)^m*Sin[a+b*x^n]^p,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,n},x] && PositiveIntegerQ[m] && RationalQ[p]


Int[(e_.+f_.*x_)^m_.*Cos[a_.+b_.*(c_+d_.*x_)^n_]^p_.,x_Symbol] :=
  1/d^(m+1)*Subst[Int[(d*e-c*f+f*x)^m*Cos[a+b*x^n]^p,x],x,c+d*x] /;
FreeQ[{a,b,c,d,e,f,n},x] && PositiveIntegerQ[m] && RationalQ[p]


Int[(f_.+g_.*x_)^m_./(a_.+b_.*Cos[d_.+e_.*x_]^2+c_.*Sin[d_.+e_.*x_]^2),x_Symbol] :=
  2*Int[(f+g*x)^m/(2*a+b+c+(b-c)*Cos[2*d+2*e*x]),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && PositiveIntegerQ[m] && NeQ[a+b] && NeQ[a+c]


Int[(f_.+g_.*x_)^m_.*Sec[d_.+e_.*x_]^2/(b_+c_.*Tan[d_.+e_.*x_]^2),x_Symbol] :=
  2*Int[(f+g*x)^m/(b+c+(b-c)*Cos[2*d+2*e*x]),x] /;
FreeQ[{b,c,d,e,f,g},x] && PositiveIntegerQ[m]


Int[(f_.+g_.*x_)^m_.*Sec[d_.+e_.*x_]^2/(b_.+a_.*Sec[d_.+e_.*x_]^2+c_.*Tan[d_.+e_.*x_]^2),x_Symbol] :=
  2*Int[(f+g*x)^m/(2*a+b+c+(b-c)*Cos[2*d+2*e*x]),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && PositiveIntegerQ[m] && NeQ[a+b] && NeQ[a+c]


Int[(f_.+g_.*x_)^m_.*Csc[d_.+e_.*x_]^2/(c_+b_.*Cot[d_.+e_.*x_]^2),x_Symbol] :=
  2*Int[(f+g*x)^m/(b+c+(b-c)*Cos[2*d+2*e*x]),x] /;
FreeQ[{b,c,d,e,f,g},x] && PositiveIntegerQ[m]


Int[(f_.+g_.*x_)^m_.*Csc[d_.+e_.*x_]^2/(c_.+b_.*Cot[d_.+e_.*x_]^2+a_.*Csc[d_.+e_.*x_]^2),x_Symbol] :=
  2*Int[(f+g*x)^m/(2*a+b+c+(b-c)*Cos[2*d+2*e*x]),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && PositiveIntegerQ[m] && NeQ[a+b] && NeQ[a+c]


Int[(e_.+f_.*x_)^m_.*Cos[c_.+d_.*x_]/(a_+b_.*Sin[c_.+d_.*x_]),x_Symbol] :=
  -I*(e+f*x)^(m+1)/(b*f*(m+1)) + 
  Int[(e+f*x)^m*E^(I*(c+d*x))/(a-Rt[a^2-b^2,2]-I*b*E^(I*(c+d*x))),x] + 
  Int[(e+f*x)^m*E^(I*(c+d*x))/(a+Rt[a^2-b^2,2]-I*b*E^(I*(c+d*x))),x] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveIntegerQ[m] && PosQ[a^2-b^2]


Int[(e_.+f_.*x_)^m_.*Sin[c_.+d_.*x_]/(a_+b_.*Cos[c_.+d_.*x_]),x_Symbol] :=
  I*(e+f*x)^(m+1)/(b*f*(m+1)) - 
  I*Int[(e+f*x)^m*E^(I*(c+d*x))/(a-Rt[a^2-b^2,2]+b*E^(I*(c+d*x))),x] - 
  I*Int[(e+f*x)^m*E^(I*(c+d*x))/(a+Rt[a^2-b^2,2]+b*E^(I*(c+d*x))),x] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveIntegerQ[m] && PosQ[a^2-b^2]


Int[(e_.+f_.*x_)^m_.*Cos[c_.+d_.*x_]/(a_+b_.*Sin[c_.+d_.*x_]),x_Symbol] :=
  -I*(e+f*x)^(m+1)/(b*f*(m+1)) + 
  I*Int[(e+f*x)^m*E^(I*(c+d*x))/(I*a-Rt[-a^2+b^2,2]+b*E^(I*(c+d*x))),x] + 
  I*Int[(e+f*x)^m*E^(I*(c+d*x))/(I*a+Rt[-a^2+b^2,2]+b*E^(I*(c+d*x))),x] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveIntegerQ[m] && NegQ[a^2-b^2]


Int[(e_.+f_.*x_)^m_.*Sin[c_.+d_.*x_]/(a_+b_.*Cos[c_.+d_.*x_]),x_Symbol] :=
  I*(e+f*x)^(m+1)/(b*f*(m+1)) + 
  Int[(e+f*x)^m*E^(I*(c+d*x))/(I*a-Rt[-a^2+b^2,2]+I*b*E^(I*(c+d*x))),x] + 
  Int[(e+f*x)^m*E^(I*(c+d*x))/(I*a+Rt[-a^2+b^2,2]+I*b*E^(I*(c+d*x))),x] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveIntegerQ[m] && NegQ[a^2-b^2]


Int[(e_.+f_.*x_)^m_.*Cos[c_.+d_.*x_]^n_/(a_+b_.*Sin[c_.+d_.*x_]),x_Symbol] :=
  1/a*Int[(e+f*x)^m*Cos[c+d*x]^(n-2),x] - 
  1/b*Int[(e+f*x)^m*Cos[c+d*x]^(n-2)*Sin[c+d*x],x] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveIntegerQ[m] && IntegerQ[n] && n>1 && EqQ[a^2-b^2]


Int[(e_.+f_.*x_)^m_.*Sin[c_.+d_.*x_]^n_/(a_+b_.*Cos[c_.+d_.*x_]),x_Symbol] :=
  1/a*Int[(e+f*x)^m*Sin[c+d*x]^(n-2),x] - 
  1/b*Int[(e+f*x)^m*Sin[c+d*x]^(n-2)*Cos[c+d*x],x] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveIntegerQ[m] && IntegerQ[n] && n>1 && EqQ[a^2-b^2]


Int[(e_.+f_.*x_)^m_.*Cos[c_.+d_.*x_]^n_/(a_+b_.*Sin[c_.+d_.*x_]),x_Symbol] :=
  a/b^2*Int[(e+f*x)^m*Cos[c+d*x]^(n-2),x] - 
  1/b*Int[(e+f*x)^m*Cos[c+d*x]^(n-2)*Sin[c+d*x],x] - 
  (a^2-b^2)/b^2*Int[(e+f*x)^m*Cos[c+d*x]^(n-2)/(a+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveIntegerQ[m] && IntegerQ[n] && n>1 && NeQ[a^2-b^2]


Int[(e_.+f_.*x_)^m_.*Sin[c_.+d_.*x_]^n_/(a_+b_.*Cos[c_.+d_.*x_]),x_Symbol] :=
  a/b^2*Int[(e+f*x)^m*Sin[c+d*x]^(n-2),x] - 
  1/b*Int[(e+f*x)^m*Sin[c+d*x]^(n-2)*Cos[c+d*x],x] - 
  (a^2-b^2)/b^2*Int[(e+f*x)^m*Sin[c+d*x]^(n-2)/(a+b*Cos[c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveIntegerQ[m] && IntegerQ[n] && n>1 && NeQ[a^2-b^2]


Int[(e_.+f_.*x_)*(A_+B_.*Sin[c_.+d_.*x_])/(a_+b_.*Sin[c_.+d_.*x_])^2,x_Symbol] :=
  -B*(e+f*x)*Cos[c+d*x]/(a*d*(a+b*Sin[c+d*x])) +
  B*f/(a*d)*Int[Cos[c+d*x]/(a+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && EqQ[a*A-b*B]


Int[(e_.+f_.*x_)*(A_+B_.*Cos[c_.+d_.*x_])/(a_+b_.*Cos[c_.+d_.*x_])^2,x_Symbol] :=
  B*(e+f*x)*Sin[c+d*x]/(a*d*(a+b*Cos[c+d*x])) -
  B*f/(a*d)*Int[Sin[c+d*x]/(a+b*Cos[c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && EqQ[a*A-b*B]


Int[(g_.+h_.*x_)^p_.*(a_+b_.*Sin[e_.+f_.*x_])^m_.*(c_+d_.*Sin[e_.+f_.*x_])^n_.,x_Symbol] :=
  a^m*c^m*Int[(g+h*x)^p*Cos[e+f*x]^(2*m)*(c+d*Sin[e+f*x])^(n-m),x] /;
FreeQ[{a,b,c,d,e,f,g,h},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0] && IntegerQ[p] && IntegerQ[m] && IGeQ[n-m,0]


Int[(g_.+h_.*x_)^p_.*(a_+b_.*Cos[e_.+f_.*x_])^m_.*(c_+d_.*Cos[e_.+f_.*x_])^n_.,x_Symbol] :=
  a^m*c^m*Int[(g+h*x)^p*Sin[e+f*x]^(2*m)*(c+d*Cos[e+f*x])^(n-m),x] /;
FreeQ[{a,b,c,d,e,f,g,h},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0] && IntegerQ[p] && IntegerQ[m] && IGeQ[n-m,0]


Int[(g_.+h_.*x_)^p_.*(a_+b_.*Sin[e_.+f_.*x_])^m_*(c_+d_.*Sin[e_.+f_.*x_])^n_,x_Symbol] :=
  a^IntPart[m]*c^IntPart[m]*(a+b*Sin[e+f*x])^FracPart[m]*(c+d*Sin[e+f*x])^FracPart[m]/Cos[e+f*x]^(2*FracPart[m])*
    Int[(g+h*x)^p*Cos[e+f*x]^(2*m)*(c+d*Sin[e+f*x])^(n-m),x] /;
FreeQ[{a,b,c,d,e,f,g,h},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0] && IntegerQ[p] && IntegerQ[2*m] && IGeQ[n-m,0]


Int[(g_.+h_.*x_)^p_.*(a_+b_.*Cos[e_.+f_.*x_])^m_*(c_+d_.*Cos[e_.+f_.*x_])^n_,x_Symbol] :=
  a^IntPart[m]*c^IntPart[m]*(a+b*Cos[e+f*x])^FracPart[m]*(c+d*Cos[e+f*x])^FracPart[m]/Sin[e+f*x]^(2*FracPart[m])*
    Int[(g+h*x)^p*Sin[e+f*x]^(2*m)*(c+d*Cos[e+f*x])^(n-m),x] /;
FreeQ[{a,b,c,d,e,f,g,h},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0] && IntegerQ[p] && IntegerQ[2*m] && IGeQ[n-m,0]


Int[Sec[v_]^m_.*(a_+b_.*Tan[v_])^n_., x_Symbol] :=
  Int[(a*Cos[v]+b*Sin[v])^n,x] /;
FreeQ[{a,b},x] && IntegersQ[m,n] && m+n==0 && OddQ[m]


Int[Csc[v_]^m_.*(a_+b_.*Cot[v_])^n_., x_Symbol] :=
  Int[(b*Cos[v]+a*Sin[v])^n,x] /;
FreeQ[{a,b},x] && IntegersQ[m,n] && m+n==0 && OddQ[m]


Int[u_.*Sin[a_.+b_.*x_]^m_.*Sin[c_.+d_.*x_]^n_.,x_Symbol] :=
  Int[ExpandTrigReduce[u,Sin[a+b*x]^m*Sin[c+d*x]^n,x],x] /;
FreeQ[{a,b,c,d},x] && PositiveIntegerQ[m,n]


Int[u_.*Cos[a_.+b_.*x_]^m_.*Cos[c_.+d_.*x_]^n_.,x_Symbol] :=
  Int[ExpandTrigReduce[u,Cos[a+b*x]^m*Cos[c+d*x]^n,x],x] /;
FreeQ[{a,b,c,d},x] && PositiveIntegerQ[m,n]


Int[Sec[a_.+b_.*x_]*Sec[c_+d_.*x_],x_Symbol] :=
  -Csc[(b*c-a*d)/d]*Int[Tan[a+b*x],x] + Csc[(b*c-a*d)/b]*Int[Tan[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && EqQ[b^2-d^2] && NeQ[b*c-a*d]


Int[Csc[a_.+b_.*x_]*Csc[c_+d_.*x_],x_Symbol] :=
  Csc[(b*c-a*d)/b]*Int[Cot[a+b*x],x] - Csc[(b*c-a*d)/d]*Int[Cot[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && EqQ[b^2-d^2] && NeQ[b*c-a*d]


Int[Tan[a_.+b_.*x_]*Tan[c_+d_.*x_],x_Symbol] :=
  -b*x/d + b/d*Cos[(b*c-a*d)/d]*Int[Sec[a+b*x]*Sec[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && EqQ[b^2-d^2] && NeQ[b*c-a*d]


Int[Cot[a_.+b_.*x_]*Cot[c_+d_.*x_],x_Symbol] :=
  -b*x/d + Cos[(b*c-a*d)/d]*Int[Csc[a+b*x]*Csc[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && EqQ[b^2-d^2] && NeQ[b*c-a*d]


Int[u_.*(a_.*Cos[v_]+b_.*Sin[v_])^n_.,x_Symbol] :=
  Int[u*(a*E^(-a/b*v))^n,x] /;
FreeQ[{a,b,n},x] && EqQ[a^2+b^2]



