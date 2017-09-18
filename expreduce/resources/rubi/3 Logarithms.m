(* ::Package:: *)

(* ::Section:: *)
(*Logarithm Function Rules*)


(* ::Subsection::Closed:: *)
(*3.1 u (a+b log(c (d (e+f x)^p)^q))^n*)


(* Int[(e_.+f_.*x_)^m_*Log[a_+b_.*x_]*(c_+d_.*x_)^n_.,x_Symbol] :=
  Int[ExpandIntegrand[Log[a+b*x],(e+f*x)^m*(c+d*x)^n,x],x] /;
FreeQ[{a,b,c,d,e,f,n},x] && FractionQ[m] && IGtQ[n,0] *)


Int[(e_.+f_.*x_)^m_*Log[a_+b_.*x_]*(c_+d_.*x_)^n_,x_Symbol] :=
  With[{k=Denominator[m]},
  k/f*Subst[Int[x^(k*(m+1)-1)*Log[-(b*e-a*f)/f+b*x^k/f]*(-(d*e-c*f)/f+d*x^k/f)^n,x],x,(e+f*x)^(1/k)]] /;
FreeQ[{a,b,c,d,e,f,n},x] && FractionQ[m] && ILtQ[n,0]


Int[Log[g_.*(h_.*(b_.*x_)^p_.)^q_.]*Log[c_+d_.*x_]/x_,x_Symbol] :=
  -Log[g*(h*(b*x)^p)^q]*PolyLog[2,-d*x] + p*q*PolyLog[3,-d*x] /;
FreeQ[{b,c,d,g,h,p,q},x] && EqQ[c,1]


Int[Log[g_.*(h_.*(b_.*x_)^p_.)^q_.]*Log[cd_*(c_+d_.*x_)]/x_,x_Symbol] :=
  -Log[g*(h*(b*x)^p)^q]*PolyLog[2,-cd*d*x] + p*q*PolyLog[3,-cd*d*x] /;
FreeQ[{b,c,cd,d,g,h,p,q},x] && EqQ[cd*c,1]


Int[Log[g_.*(h_.*(b_.*x_)^p_.)^q_.]*Log[i_.*(j_.*(c_+d_.*x_)^r_.)^s_.]/x_,x_Symbol] :=
  r*s*Int[Log[g*(h*(b*x)^p)^q]*Log[1+d*x]/x,x] - 
  (r*s*Log[1+d*x]-Log[i*(j*(1+d*x)^r)^s])*Int[Log[g*(h*(b*x)^p)^q]/x,x]/;
FreeQ[{b,c,d,g,h,i,j,p,q,r,s},x] && EqQ[c,1] && NeQ[1+d*x,i*(j*(1+d*x)^r)^s]


Int[Log[g_.*(h_.*(b_.*x_)^p_.)^q_.]*Log[i_.*(j_.*(c_.+d_.*x_)^r_.)^s_.]/x_,x_Symbol] :=
  Log[g*(h*(b*x)^p)^q]^2*Log[i*(j*(c+d*x)^r)^s]/(2*p*q) - d*r*s/(2*p*q)*Int[Log[g*(h*(b*x)^p)^q]^2/(c+d*x),x]/;
FreeQ[{b,c,d,g,h,i,j,p,q,r,s},x] && NeQ[c,1]


Int[Log[g_.*(h_.*(a_.+b_.*x_)^p_.)^q_.]*Log[i_.*(j_.*(c_.+d_.*x_)^r_.)^s_.]/x_,x_Symbol] :=
  Log[x]*Log[g*(h*(a+b*x)^p)^q]*Log[i*(j*(c+d*x)^r)^s] - 
  d*r*s*Int[Log[x]*Log[g*(h*(a+b*x)^p)^q]/(c+d*x),x] - 
  d*p*q*Int[Log[x]*Log[i*(j*(c+d*x)^r)^s]/(c+d*x),x]/;
FreeQ[{a,b,c,d,g,h,i,j,p,q,r,s},x] && EqQ[b*c-a*d,0]


Int[Log[a_+b_.*x_]*Log[c_+d_.*x_]/x_,x_Symbol] :=
  Log[-b*x/a]*Log[a+b*x]*Log[c+d*x] + 
  1/2*Log[-b*x/a]*Log[a*(c+d*x)/(c*(a+b*x))]^2 + 
  1/2*Log[-(b*c-a*d)/(d*(a+b*x))]*Log[a*(c+d*x)/(c*(a+b*x))]^2 - 
  1/2*Log[a*(c+d*x)/(c*(a+b*x))]^2*Log[(b*c-a*d)*x/(c*(a+b*x))] - 
  Log[-b*x/a]*Log[a+b*x]*Log[1+d*x/c] + 
  Log[-(d*x/c)]*Log[a+b*x]*Log[1+d*x/c] - 
  Log[-b*x/a]*Log[a*(c+d*x)/(c*(a+b*x))]*Log[1+d*x/c] + 
  Log[-d*x/c]*Log[a*(c+d*x)/(c*(a+b*x))]*Log[1+d*x/c] + 
  1/2*Log[-b*x/a]*Log[1+d*x/c]^2 - 
  1/2*Log[-d*x/c]*Log[1+d*x/c]^2 + 
  Log[c+d*x]*PolyLog[2,1+b*x/a] - 
  Log[a*(c+d*x)/(c*(a+b*x))]*PolyLog[2,1+b*x/a] - 
  Log[a*(c+d*x)/(c*(a+b*x))]*PolyLog[2,a*(c+d*x)/(c*(a+b*x))] + 
  Log[a*(c+d*x)/(c*(a+b*x))]*PolyLog[2,b*(c+d*x)/(d*(a+b*x))] + 
  Log[a+b*x]*PolyLog[2,1+d*x/c] + 
  Log[a*(c+d*x)/(c*(a+b*x))]*PolyLog[2,1+d*x/c] - 
  PolyLog[3,1+b*x/a] +
  PolyLog[3,a*(c+d*x)/(c*(a+b*x))] - 
  PolyLog[3,b*(c+d*x)/(d*(a+b*x))] - 
  PolyLog[3,1+d*x/c]/;
FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0]


Int[Log[v_]*Log[w_]/x_,x_Symbol] :=
  Int[Log[ExpandToSum[v,x]]*Log[ExpandToSum[w,x]]/x,x] /;
LinearQ[{v,w},x] && Not[LinearMatchQ[{v,w},x]]


Int[Log[g_.*(h_.*(a_.+b_.*x_)^p_.)^q_.]*Log[i_.*(j_.*(c_.+d_.*x_)^r_.)^s_.]/x_,x_Symbol] :=
  p*q*Int[Log[a+b*x]*Log[i*(j*(c+d*x)^r)^s]/x,x] - 
  (p*q*Log[a+b*x]-Log[g*(h*(a+b*x)^p)^q])*Int[Log[i*(j*(c+d*x)^r)^s]/x,x]/;
FreeQ[{a,b,c,d,g,h,i,j,p,q,r,s},x] && NeQ[b*c-a*d,0] && NeQ[a+b*x,g*(h*(a+b*x)^p)^q]


Int[Log[g_.*(h_.*(a_.+b_.*x_)^p_.)^q_.]*Log[i_.*(j_.*(c_.+d_.*x_)^r_.)^s_.]/(e_+f_.*x_),x_Symbol] :=
  1/f*Subst[Int[Log[g*(h*Simp[-(b*e-a*f)/f+b*x/f,x]^p)^q]*Log[i*(j*Simp[-(d*e-c*f)/f+d*x/f,x]^r)^s]/x,x],x,e+f*x]/;
FreeQ[{a,b,c,d,e,f,g,h,i,j,p,q,r,s},x]


Int[(e_.+f_.*x_)^m_.*Log[g_.*(h_.*(a_.+b_.*x_)^p_.)^q_.]*Log[i_.*(j_.*(c_.+d_.*x_)^r_.)^s_.],x_Symbol] :=
  (e+f*x)^(m+1)*Log[g*(h*(a+b*x)^p)^q]*Log[i*(j*(c+d*x)^r)^s]/(f*(m+1)) - 
  d*r*s/(f*(m+1))*Int[(e+f*x)^(m+1)*Log[g*(h*(a+b*x)^p)^q]/(c+d*x),x] - 
  b*p*q/(f*(m+1))*Int[(e+f*x)^(m+1)*Log[i*(j*(c+d*x)^r)^s]/(a+b*x),x]/;
FreeQ[{a,b,c,d,e,f,g,h,i,j,m,p,q,r,s},x] && m!=-1 && RationalQ[m]


Int[(e_.+f_.*x_)^m_.*Log[g_.*(h_.*(a_.+b_.*x_)^p_.)^q_.]*Log[i_.*(j_.*(c_.+d_.*x_)^r_.)^s_.],x_Symbol] :=
  Defer[Int][(e+f*x)^m*Log[g*(h*(a+b*x)^p)^q]*Log[i*(j*(c+d*x)^r)^s],x]/;
FreeQ[{a,b,c,d,e,f,g,h,i,j,m,p,q,r,s},x]


Int[Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.],x_Symbol] :=
  (e+f*x)*Log[c*(d*(e+f*x)^p)^q]/f - p*q*x /;
FreeQ[{c,d,e,f,p,q},x]


Int[(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_,x_Symbol] :=
  (e+f*x)*(a+b*Log[c*(d*(e+f*x)^p)^q])^n/f - b*n*p*q*Int[(a+b*Log[c*(d*(e+f*x)^p)^q])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,p,q},x] && GtQ[n,0]


Int[1/Log[d_.*(e_.+f_.*x_)],x_Symbol] :=
  LogIntegral[d*(e+f*x)]/(d*f) /;
FreeQ[{d,e,f},x]


Int[1/(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.]),x_Symbol] :=
  (e+f*x)/(b*f*p*q*E^(a/(b*p*q))*(c*(d*(e+f*x)^p)^q)^(1/(p*q)))*ExpIntegralEi[(a+b*Log[c*(d*(e+f*x)^p)^q])/(b*p*q)] /;
FreeQ[{a,b,c,d,e,f,p,q},x]


Int[1/Sqrt[a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.]],x_Symbol] :=
  Sqrt[Pi]*Rt[b*p*q,2]*(e+f*x)/(b*f*p*q*E^(a/(b*p*q))*(c*(d*(e+f*x)^p)^q)^(1/(p*q)))*
    Erfi[Sqrt[a+b*Log[c*(d*(e+f*x)^p)^q]]/Rt[b*p*q,2]] /;
FreeQ[{a,b,c,d,e,f,p,q},x] && PosQ[b*p*q]


Int[1/Sqrt[a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.]],x_Symbol] :=
  Sqrt[Pi]*Rt[-b*p*q,2]*(e+f*x)/(b*f*p*q*E^(a/(b*p*q))*(c*(d*(e+f*x)^p)^q)^(1/(p*q)))*
    Erf[Sqrt[a+b*Log[c*(d*(e+f*x)^p)^q]]/Rt[-b*p*q,2]] /;
FreeQ[{a,b,c,d,e,f,p,q},x] && NegQ[b*p*q]


Int[(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_,x_Symbol] :=
  (e+f*x)*(a+b*Log[c*(d*(e+f*x)^p)^q])^(n+1)/(b*f*p*q*(n+1)) - 
  1/(b*p*q*(n+1))*Int[(a+b*Log[c*(d*(e+f*x)^p)^q])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,p,q},x] && LtQ[n,-1]


Int[(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_,x_Symbol] :=
  (e+f*x)*(a+b*Log[c*(d*(e+f*x)^p)^q])^n/
    (f*E^(a/(b*p*q))*(c*(d*(e+f*x)^p)^q)^(1/(p*q))*(-(a+b*Log[c*(d*(e+f*x)^p)^q])/(b*p*q))^n)*
    Gamma[n+1,-(a+b*Log[c*(d*(e+f*x)^p)^q])/(b*p*q)] /;
FreeQ[{a,b,c,d,e,f,p,q},x] && Not[IntegerQ[2*n]]


Int[1/((g_.+h_.*x_)*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])),x_Symbol] :=
  Log[RemoveContent[a+b*Log[c*(d*(e+f*x)^p)^q],x]]/(b*h*p*q) /;
FreeQ[{a,b,c,d,e,f,g,h,p,q},x] && EqQ[f*g-e*h,0]


Int[(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_./(g_.+h_.*x_),x_Symbol] :=
  (a+b*Log[c*(d*(e+f*x)^p)^q])^(n+1)/(b*h*p*q*(n+1)) /;
FreeQ[{a,b,c,d,e,f,g,h,n,p,q},x] && EqQ[f*g-e*h,0] && NeQ[n,-1]


Int[(g_.+h_.*x_)^m_.*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_.,x_Symbol] :=
  (g+h*x)^(m+1)*(a+b*Log[c*(d*(e+f*x)^p)^q])^n/(h*(m+1)) - 
  b*n*p*q/(m+1)*Int[(g+h*x)^m*(a+b*Log[c*(d*(e+f*x)^p)^q])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,p,q},x] && EqQ[f*g-e*h,0] && NeQ[m,-1] && GtQ[n,0]


Int[(g_.+h_.*x_)^m_./Log[d_.*(e_.+f_.*x_)^p_.],x_Symbol] :=
  (h/f)^(p-1)*LogIntegral[d*(e+f*x)^p]/(d*f*p) /;
FreeQ[{d,e,f,g,h,m,p},x] && EqQ[m-(p-1),0] && EqQ[f*g-e*h,0] && (IntegerQ[p] || PositiveQ[h/f])


Int[(g_.+h_.*x_)^m_/Log[d_.*(e_.+f_.*x_)^p_.],x_Symbol] :=
  (g+h*x)^(p-1)/(e+f*x)^(p-1)*Int[(e+f*x)^(p-1)/Log[d*(e+f*x)^p],x] /;
FreeQ[{d,e,f,g,h,m,p},x] && EqQ[m-(p-1),0] && EqQ[f*g-e*h,0] && Not[IntegerQ[p] || PositiveQ[h/f]]


Int[(g_.+h_.*x_)^m_./(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.]),x_Symbol] :=
  (g+h*x)^(m+1)/(b*h*p*q*E^(a*(m+1)/(b*p*q))*(c*(d*(e+f*x)^p)^q)^((m+1)/(p*q)))*
    ExpIntegralEi[(m+1)*(a+b*Log[c*(d*(e+f*x)^p)^q])/(b*p*q)] /;
FreeQ[{a,b,c,d,e,f,g,h,m,p,q},x] && EqQ[f*g-e*h,0] && NeQ[m,-1]


Int[(g_.+h_.*x_)^m_./Sqrt[a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.]],x_Symbol] :=
  Sqrt[Pi]*(g+h*x)^(m+1)/(b*h*p*q*Rt[(m+1)/(b*p*q),2]*E^(a*(m+1)/(b*p*q))*(c*(d*(e+f*x)^p)^q)^((m+1)/(p*q)))*
    Erfi[Rt[(m+1)/(b*p*q),2]*Sqrt[a+b*Log[c*(d*(e+f*x)^p)^q]]] /;
FreeQ[{a,b,c,d,e,f,g,h,m,p,q},x] && EqQ[f*g-e*h,0] && NeQ[m,-1] && PosQ[(m+1)/(b*p*q)]


Int[(g_.+h_.*x_)^m_./Sqrt[a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.]],x_Symbol] :=
  Sqrt[Pi]*(g+h*x)^(m+1)/(b*h*p*q*Rt[-(m+1)/(b*p*q),2]*E^(a*(m+1)/(b*p*q))*(c*(d*(e+f*x)^p)^q)^((m+1)/(p*q)))*
    Erf[Rt[-(m+1)/(b*p*q),2]*Sqrt[a+b*Log[c*(d*(e+f*x)^p)^q]]] /;
FreeQ[{a,b,c,d,e,f,g,h,m,p,q},x] && EqQ[f*g-e*h,0] && NeQ[m,-1] && NegQ[(m+1)/(b*p*q)]


Int[(g_.+h_.*x_)^m_.*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_,x_Symbol] :=
  (g+h*x)^(m+1)*(a+b*Log[c*(d*(e+f*x)^p)^q])^(n+1)/(b*h*p*q*(n+1)) - 
  (m+1)/(b*p*q*(n+1))*Int[(g+h*x)^m*(a+b*Log[c*(d*(e+f*x)^p)^q])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,p,q},x] && EqQ[f*g-e*h,0] && NeQ[m,-1] && LtQ[n,-1]


Int[(g_.+h_.*x_)^m_.*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_.,x_Symbol] :=
  (g+h*x)^(m+1)*(a+b*Log[c*(d*(e+f*x)^p)^q])^n/
    (h*(m+1)*E^(a*(m+1)/(b*p*q))*(c*(d*(e+f*x)^p)^q)^((m+1)/(p*q))*(-(m+1)*(a+b*Log[c*(d*(e+f*x)^p)^q])/(b*p*q))^n)*
    Gamma[n+1,-(m+1)*(a+b*Log[c*(d*(e+f*x)^p)^q])/(b*p*q)] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n,p},x] && EqQ[f*g-e*h,0] && NeQ[m,-1]


Int[Log[c_.*(e_.+f_.*x_)]/(g_.+h_.*x_),x_Symbol] :=
  -1/h*PolyLog[2,-Together[c*f/h]*(g+h*x)] /;
FreeQ[{c,e,f,g,h},x] && EqQ[h+c*(f*g-e*h),0]


Int[(a_.+b_.*Log[c_.*(e_.+f_.*x_)])/(g_.+h_.*x_),x_Symbol] :=
  (a+b*Log[c*(e-f*g/h)])*Log[g+h*x]/h + b*Int[Log[-h*(e+f*x)/(f*g-e*h)]/(g+h*x),x] /;
FreeQ[{a,b,c,e,f,g,h},x] && NeQ[h+c*(f*g-e*h),0] && PositiveQ[c*(e-f*g/h)]


Int[(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_./(g_.+h_.*x_),x_Symbol] :=
  (a+b*Log[c*(d*(e+f*x)^p)^q])^n/h*Log[f*(g+h*x)/(f*g-e*h)] - 
  b*f*n*p*q/h*Int[(a+b*Log[c*(d*(e+f*x)^p)^q])^(n-1)*Log[f*(g+h*x)/(f*g-e*h)]/(e+f*x),x] /;
FreeQ[{a,b,c,d,e,f,g,h,p,q},x] && NeQ[f*g-e*h,0] && PositiveIntegerQ[n]


Int[(g_.+h_.*x_)^m_.*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.]),x_Symbol] :=
  (g+h*x)^(m+1)*(a+b*Log[c*(d*(e+f*x)^p)^q])/(h*(m+1)) - 
  b*f*p*q/(h*(m+1))*Int[(g+h*x)^(m+1)/(e+f*x),x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,p,q},x] && NeQ[f*g-e*h,0] && NeQ[m,-1]


Int[(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_/(g_.+h_.*x_)^2,x_Symbol] :=
  (e+f*x)*(a+b*Log[c*(d*(e+f*x)^p)^q])^n/((f*g-e*h)*(g+h*x)) - 
  b*f*n*p*q/(f*g-e*h)*Int[(a+b*Log[c*(d*(e+f*x)^p)^q])^(n-1)/(g+h*x),x] /;
FreeQ[{a,b,c,d,e,f,g,h,p,q},x] && NeQ[f*g-e*h,0] && GtQ[n,0]


Int[(g_.+h_.*x_)^m_.*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_,x_Symbol] :=
  (g+h*x)^(m+1)*(a+b*Log[c*(d*(e+f*x)^p)^q])^n/(h*(m+1)) - 
  b*f*n*p*q/(h*(m+1))*Int[(g+h*x)^(m+1)*(a+b*Log[c*(d*(e+f*x)^p)^q])^(n-1)/(e+f*x),x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,p,q},x] && NeQ[f*g-e*h,0] && GtQ[n,0] && NeQ[m,-1] && IntegersQ[2*m,2*n] && 
  (n==1 || Not[PositiveIntegerQ[m]] || n==2 && NeQ[m,1])


Int[(g_.+h_.*x_)^m_./(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.]),x_Symbol] :=
  Int[ExpandIntegrand[(g+h*x)^m/(a+b*Log[c*(d*(e+f*x)^p)^q]),x],x] /;
FreeQ[{a,b,c,d,e,f,g,h,p,q},x] && NeQ[f*g-e*h,0] && PositiveIntegerQ[m]


Int[(g_.+h_.*x_)^m_.*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_,x_Symbol] :=
  (e+f*x)*(g+h*x)^m*(a+b*Log[c*(d*(e+f*x)^p)^q])^(n+1)/(b*f*p*q*(n+1)) + 
  m*(f*g-e*h)/(b*f*p*q*(n+1))*Int[(g+h*x)^(m-1)*(a+b*Log[c*(d*(e+f*x)^p)^q])^(n+1),x] - 
  (m+1)/(b*p*q*(n+1))*Int[(g+h*x)^m*(a+b*Log[c*(d*(e+f*x)^p)^q])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,g,h,p,q},x] && NeQ[f*g-e*h,0] && LtQ[n,-1] && GtQ[m,0]


Int[(g_.+h_.*x_)^m_.*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_,x_Symbol] :=
  Int[ExpandIntegrand[(g+h*x)^m*(a+b*Log[c*(d*(e+f*x)^p)^q])^n,x],x] /;
FreeQ[{a,b,c,d,e,f,g,h,n,p,q},x] && NeQ[f*g-e*h,0] && PositiveIntegerQ[m]


Int[u_^m_.*(a_.+b_.*Log[c_.*(d_.*v_^p_)^q_.])^n_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*(a+b*Log[c*(d*ExpandToSum[v,x]^p)^q])^n,x] /;
FreeQ[{a,b,c,d,m,n,p,q},x] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]


Int[(g_.+h_.*x_)^m_.*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_.,x_Symbol] :=
  Defer[Int][(g+h*x)^m*(a+b*Log[c*(d*(e+f*x)^p)^q])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n,p,q},x]


Int[Log[c_./(e_.+f_.*x_)]/((g_.+h_.*x_)*(i_.+j_.*x_)),x_Symbol] :=
  f/(h*(f*i-e*j))*PolyLog[2,Simplify[f*(i+j*x)/(j*(e+f*x))]] /;
FreeQ[{c,e,f,g,h,i,j},x] && EqQ[f*g-e*h,0] && EqQ[f*i+j*(c-e),0]


Int[(a_+b_.*Log[c_./(e_.+f_.*x_)])/((g_.+h_.*x_)*(i_.+j_.*x_)),x_Symbol] :=
  a*Int[1/((g+h*x)*(i+j*x)),x] + b*Int[Log[c/(e+f*x)]/((g+h*x)*(i+j*x)),x] /;
FreeQ[{a,b,c,e,f,g,h,i,j},x] && EqQ[f*g-e*h,0] && EqQ[f*i+j*(c-e),0]


Int[(i_.+j_.*x_)^m_.*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])/(g_.+h_.*x_),x_Symbol] :=
  With[{u=IntHide[(i+j*x)^m/(g+h*x),x]},
  Dist[a+b*Log[c*(d*(e+f*x)^p)^q],u] - b*h*p*q*Int[SimplifyIntegrand[u/(g+h*x),x],x]] /;
FreeQ[{a,b,c,d,e,f,g,h,i,j,p,q},x] && EqQ[f*g-e*h,0] && IntegerQ[m+1/2]


Int[(i_.+j_.*x_)^m_.*(a_.+b_.*Log[c_.*(e_.+f_.*x_)])^n_./(g_.+h_.*x_),x_Symbol] :=
  1/(c^m*f^m*h)*Subst[Int[(a+b*x)^n*(c*f*i-c*e*j+j*E^x)^m,x],x,Log[c*(e+f*x)]] /;
FreeQ[{a,b,c,e,f,g,h,i,j,n},x] && EqQ[f*g-e*h,0] && PositiveIntegerQ[m] && (IntegerQ[n] || m>0)


Int[(i_.+j_.*x_)^m_.*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_./(g_.+h_.*x_),x_Symbol] :=
  With[{u=ExpandIntegrand[(a+b*Log[c*(d*(e+f*x)^p)^q])^n,(i+j*x)^m/(g+h*x),x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{a,b,c,d,e,f,g,h,i,j,p,q},x] && IntegerQ[m] && PositiveIntegerQ[n]


Int[(i_.+j_.*x_)^m_.*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_./(g_.+h_.*x_),x_Symbol] :=
  Defer[Int][(i+j*x)^m*(a+b*Log[c*(d*(e+f*x)^p)^q])^n/(g+h*x),x] /;
FreeQ[{a,b,c,d,e,f,g,h,i,j,m,n,p,q},x]


Int[Log[j_.*(k_.+m_.*x_)]/(g_.+h_.*x_)*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_.,x_Symbol] :=
  -PolyLog[2,Together[1-j*(k+m*x)]]/h*(a+b*Log[c*(d*(e+f*x)^p)^q])^n + 
  b*f*n*p*q/h*Int[PolyLog[2,Together[1-j*(k+m*x)]]/(e+f*x)*(a+b*Log[c*(d*(e+f*x)^p)^q])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,g,h,j,k,m,p,q},x] && EqQ[h-h*j*k+g*j*m,0] && GtQ[n,0]


Int[Log[i_.*(j_.*(k_.+m_.*x_)^r_.)^s_.]*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_./(g_.+h_.*x_),x_Symbol] :=
  Log[i*(j*(k+m*x)^r)^s]*(a+b*Log[c*(d*(e+f*x)^p)^q])^(n+1)/(b*h*p*q*(n+1)) - 
  m*r*s/(b*h*p*q*(n+1))*Int[(a+b*Log[c*(d*(e+f*x)^p)^q])^(n+1)/(k+m*x),x] /;
FreeQ[{a,b,c,d,e,f,g,h,i,j,k,m,n,p,q,r,s},x] && EqQ[f*g-e*h,0] && NeQ[n,-1]


Int[Log[c_./(e_.+f_.*x_)]/(g_+h_.*x_^2),x_Symbol] :=
  -f/(2*e*h)*PolyLog[2,Simplify[(-e+f*x)/(e+f*x)]] /;
FreeQ[{c,e,f,g,h},x] && EqQ[f^2*g+e^2*h,0] && EqQ[c-2*e,0]


Int[(a_.+b_.*Log[c_./(e_.+f_.*x_)])/(g_+h_.*x_^2),x_Symbol] :=
  (a+b*Log[c/(2*e)])*Int[1/(g+h*x^2),x] + b*Int[Log[2*e/(e+f*x)]/(g+h*x^2),x] /;
FreeQ[{c,e,f,g,h},x] && EqQ[f^2*g+e^2*h,0] && PositiveQ[c/(2*e)] && (NeQ[c-2*e,0] || NeQ[a,0])


Int[(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])/(g_.+h_.*x_+i_.*x_^2),x_Symbol] :=
  e*f*Int[(a+b*Log[c*(d*(e+f*x)^p)^q])/((e+f*x)*(f*g+e*i*x)),x] /;
FreeQ[{a,b,c,d,e,f,g,h,i,p,q},x] && EqQ[f^2*g-e*f*h+e^2*i,0]


Int[(a_.+b_.*Log[c_.*(d_.*(e_+f_.*x_)^p_.)^q_.])/(g_+i_.*x_^2),x_Symbol] :=
  e*f*Int[(a+b*Log[c*(d*(e+f*x)^p)^q])/((e+f*x)*(f*g+e*i*x)),x] /;
FreeQ[{a,b,c,d,e,f,g,i,p,q},x] && EqQ[f^2*g+e^2*i,0]


Int[(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])/Sqrt[g_+h_.*x_^2],x_Symbol] :=
  With[{u=IntHide[1/Sqrt[g+h*x^2],x]},  
  u*(a+b*Log[c*(d*(e+f*x)^p)^q]) - b*f*p*q*Int[SimplifyIntegrand[u/(e+f*x),x],x]] /;
FreeQ[{a,b,c,d,e,f,g,h,p,q},x] && PositiveQ[g]


Int[(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])/(Sqrt[g1_+h1_.*x_]*Sqrt[g2_+h2_.*x_]),x_Symbol] :=
  With[{u=IntHide[1/Sqrt[g1*g2+h1*h2*x^2],x]},  
  u*(a+b*Log[c*(d*(e+f*x)^p)^q]) - b*f*p*q*Int[SimplifyIntegrand[u/(e+f*x),x],x]] /;
FreeQ[{a,b,c,d,e,f,g1,h1,g2,h2,p,q},x] && EqQ[g2*h1+g1*h2,0] && PositiveQ[g1] && PositiveQ[g2]


Int[(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])/Sqrt[g_+h_.*x_^2],x_Symbol] :=
  Sqrt[1+h/g*x^2]/Sqrt[g+h*x^2]*Int[(a+b*Log[c*(d*(e+f*x)^p)^q])/Sqrt[1+h/g*x^2],x] /;
FreeQ[{a,b,c,d,e,f,g,h,p,q},x] && Not[PositiveQ[g]]


Int[(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])/(Sqrt[g1_+h1_.*x_]*Sqrt[g2_+h2_.*x_]),x_Symbol] :=
  Sqrt[1+h1*h2/(g1*g2)*x^2]/(Sqrt[g1+h1*x]*Sqrt[g2+h2*x])*Int[(a+b*Log[c*(d*(e+f*x)^p)^q])/Sqrt[1+h1*h2/(g1*g2)*x^2],x] /;
FreeQ[{a,b,c,d,e,f,g1,h1,g2,h2,p,q},x] && EqQ[g2*h1+g1*h2,0]


Int[Log[1+i_.*(j_.+k_.*x_)^m_.]/(g_.+h_.*x_)*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_.,x_Symbol] :=
  -PolyLog[2,-i*(j+k*x)^m]/(h*m)*(a+b*Log[c*(d*(e+f*x)^p)^q])^n + 
  b*f*n*p*q/(h*m)*Int[PolyLog[2,-i*(j+k*x)^m]/(e+f*x)*(a+b*Log[c*(d*(e+f*x)^p)^q])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,g,h,i,j,k,m,p,q},x] && GtQ[n,0] && EqQ[h*j-g*k,0]


Int[PolyLog[r_,i_.*(j_.+k_.*x_)^m_.]/(g_.+h_.*x_)*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_.,x_Symbol] :=
  PolyLog[r+1,i*(j+k*x)^m]/(h*m)*(a+b*Log[c*(d*(e+f*x)^p)^q])^n - 
  b*f*n*p*q/(h*m)*Int[PolyLog[r+1,i*(j+k*x)^m]/(e+f*x)*(a+b*Log[c*(d*(e+f*x)^p)^q])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,g,h,i,j,k,m,p,q,r},x] && GtQ[n,0] && EqQ[h*j-g*k,0]


Int[Px_.*F_[g_.+h_.*x_]^m_.*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.]),x_Symbol] :=
  With[{u=IntHide[Px*F[g+h*x]^m,x]},
  Dist[(a+b*Log[c*(d*(e+f*x)^p)^q]),u,x] - b*f*p*q*Int[SimplifyIntegrand[u/(e+f*x),x],x]] /;
FreeQ[{a,b,c,d,e,f,g,h,p,q},x] && PolynomialQ[Px,x] && PositiveIntegerQ[m] && 
  MemberQ[{Log,ArcSin,ArcCos,ArcTan,ArcCot,ArcSinh, ArcCosh,ArcTanh, ArcCoth},F]


Int[(a_.+b_.*Log[c_.*(d_.*(e_+f_.*x_^m_)^p_.)^q_.])^n_./x_,x_Symbol] :=
  1/m*Subst[Int[(a+b*Log[c*(d*(e+f*x)^p)^q])^n/x,x],x,x^m] /;
FreeQ[{a,b,c,d,e,f,m,n,p,q},x] && PositiveIntegerQ[n]


Int[(a_.+b_.*Log[c_.*(d_.*(x_^m_*(f_+e_.*x_^r_.))^p_.)^q_.])^n_./x_,x_Symbol] :=
  1/m*Subst[Int[(a+b*Log[c*(d*(e+f*x)^p)^q])^n/x,x],x,x^m] /;
FreeQ[{a,b,c,d,e,f,m,n,p,q},x] && EqQ[m+r,0] && PositiveIntegerQ[n]


Int[x_^r1_.*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_^r_)^p_.)^q_.])^n_.,x_Symbol] :=
  1/r*Subst[Int[(a+b*Log[c*(d*(e+f*x)^p)^q])^n,x],x,x^r] /;
FreeQ[{a,b,c,d,e,f,n,p,q,r},x] && EqQ[r1-(r-1),0]


Int[x_^r1_.*(g_.+h_.*x_^r_)^m_.*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_^r_)^p_.)^q_.])^n_.,x_Symbol] :=
  1/r*Subst[Int[(g+h*x)^m*(a+b*Log[c*(d*(e+f*x)^p)^q])^n,x],x,x^r] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n,p,q,r},x] && EqQ[r1-(r-1),0]


Int[(a_.+b_.*Log[c_.*x_^n_.])/(d_+e_.*x_^2),x_Symbol] :=
  With[{u=IntHide[1/(d+e*x^2),x]},  
  Dist[(a+b*Log[c*x^n]),u] - b*n*Int[u/x,x]] /;
FreeQ[{a,b,c,d,e,n},x]


Int[Log[c_.*(a_.+b_.*x_^mn_)]/(x_*(d_+e_.*x_^n_.)),x_Symbol] :=
  1/(d*n)*PolyLog[2,-Together[b*c*(d+e*x^n)/(d*x^n)]] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[n+mn,0] && EqQ[d-a*c*d+b*c*e,0]


Int[Log[c_.*x_^mn_*(b_.+a_.*x_^n_.)]/(x_*(d_+e_.*x_^n_.)),x_Symbol] :=
  1/(d*n)*PolyLog[2,-Together[b*c*(d+e*x^n)/(d*x^n)]] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[n+mn,0] && EqQ[d-a*c*d+b*c*e,0]


Int[Px_*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[Px*(a+b*Log[c*(d*(e+f*x)^p)^q])^n,x],x] /;
FreeQ[{a,b,c,d,e,f,n,p,q},x] && PolynomialQ[Px,x]


Int[RFx_*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_.,x_Symbol] :=
  With[{u=ExpandIntegrand[(a+b*Log[c*(d*(e+f*x)^p)^q])^n,RFx,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{a,b,c,d,e,f,p,q},x] && RationalFunctionQ[RFx,x] && PositiveIntegerQ[n]


Int[RFx_*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_.,x_Symbol] :=
  With[{u=ExpandIntegrand[RFx*(a+b*Log[c*(d*(e+f*x)^p)^q])^n,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{a,b,c,d,e,f,p,q},x] && RationalFunctionQ[RFx,x] && PositiveIntegerQ[n]


Int[u_.*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_+g_.*x_^2)^p_.)^q_.])^n_.,x_Symbol] :=
  Int[u*(a+b*Log[c*(d*(f+2*g*x)^(2*p)/(4^p*g^p))^q])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,q,n},x] && EqQ[f^2-4*e*g,0] && IntegerQ[p]


Int[u_.*(a_.+b_.*Log[c_.*(d_.*v_^p_.)^q_.])^n_.,x_Symbol] :=
  Int[u*(a+b*Log[c*(d*ExpandToSum[v,x]^p)^q])^n,x] /;
FreeQ[{a,b,c,d,n,p,q},x] && LinearQ[v,x] && 
  Not[MatchQ[c*(d*v^p)^q, cc_.*(dd_.*(e_.+f_.*x)^pp_.)^qq_. /; FreeQ[{cc,dd,e,f,pp,qq},x]]]


Int[Log[a_.*(b_.*(c_.*x_^n_.)^p_)^q_]^r_.,x_Symbol] :=
  Subst[Int[Log[x^(n*p*q)]^r,x],x^(n*p*q),a*(b*(c*x^n)^p)^q] /;
FreeQ[{a,b,c,n,p,q,r},x]


Int[x_^m_.*Log[a_.*(b_.*(c_.*x_^n_.)^p_)^q_]^r_.,x_Symbol] :=
  Subst[Int[x^m*Log[x^(n*p*q)]^r,x],x^(n*p*q),a*(b*(c*x^n)^p)^q] /;
FreeQ[{a,b,c,m,n,p,q,r},x] && NeQ[m,-1] && Not[x^(n*p*q)===a*(b*(c*x^n)^p)^q]





(* ::Subsection::Closed:: *)
(*3.2 u log(e (f (a+b x)^p (c+d x)^q)^r)^s*)


Int[u_.*Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^s_.,x_Symbol] :=
  Int[u*Log[e*(b^p*f/d^p*(c+d*x)^(p+q))^r]^s,x] /;
FreeQ[{a,b,c,d,e,f,p,q,r,s},x] && EqQ[b*c-a*d,0] && IntegerQ[p]


Int[Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^s_.,x_Symbol] :=
  (a+b*x)*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^s/b - 
  r*s/b*Int[(b*c*p+a*d*q+b*d*(p+q)*x)*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^(s-1)/(c+d*x),x] /;
FreeQ[{a,b,c,d,e,f,p,q,r,s},x] && NeQ[b*c-a*d,0] && IGtQ[s,0]


Int[Log[e_.*(a_.+b_.*x_)/(c_.+d_.*x_)]/(g_.+h_.*x_),x_Symbol] :=
  1/h*PolyLog[2,Together[c-a*e]/(c+d*x)] /;
FreeQ[{a,b,c,d,e,g,h},x] && NeQ[b*c-a*d,0] && EqQ[d*g-c*h,0] && EqQ[d-b*e,0]


Int[Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^s_./(g_.+h_.*x_),x_Symbol] :=
  -Log[-(b*c-a*d)/(d*(a+b*x))]*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^s/h + 
  p*r*s (b*c-a*d)/h*Int[Log[-(b*c-a*d)/(d*(a+b*x))]*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^(s-1)/((a+b*x)*(c+d*x)),x] /;
FreeQ[{a,b,c,d,e,f,g,h,p,q,r,s},x] && NeQ[b*c-a*d,0] && IGtQ[s,0] && EqQ[b*g-a*h,0] && EqQ[p+q,0]


Int[Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]/(g_.+h_.*x_),x_Symbol] :=
  Log[g+h*x]*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]/h - 
  b*p*r/h*Int[Log[g+h*x]/(a+b*x),x] - 
  d*q*r/h*Int[Log[g+h*x]/(c+d*x),x] /;
FreeQ[{a,b,c,d,e,f,g,h,p,q,r},x] && NeQ[b*c-a*d,0]


Int[Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^s_/(g_.+h_.*x_),x_Symbol] :=
  d/h*Int[Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^s/(c+d*x),x] - 
  (d*g-c*h)/h*Int[Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^s/((c+d*x)*(g+h*x)),x] /;
FreeQ[{a,b,c,d,e,f,g,h,p,q,r,s},x] && NeQ[b*c-a*d,0] && IGtQ[s,1]


Int[Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^s_./(g_.+h_.*x_)^2,x_Symbol] :=
  (a+b*x)*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^s/((b*g-a*h)*(g+h*x)) - 
  p*r*s*(b*c-a*d)/(b*g-a*h)*Int[Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^(s-1)/((c+d*x)*(g+h*x)),x] /;
FreeQ[{a,b,c,d,e,f,g,h,p,q,r,s},x] && NeQ[b*c-a*d,0] && IGtQ[s,0] && EqQ[p+q,0] && NeQ[b*g-a*h,0]


Int[Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^s_/(g_.+h_.*x_)^3,x_Symbol] :=
  d/(d*g-c*h)*Int[Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^s/(g+h*x)^2,x] - 
  h/(d*g-c*h)*Int[(c+d*x)*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^s/(g+h*x)^3,x] /;
FreeQ[{a,b,c,d,e,f,g,h,p,q,r,s},x] && NeQ[b*c-a*d,0] && IGtQ[s,0] && EqQ[p+q,0] && EqQ[b*g-a*h,0] && NeQ[d*g-c*h,0]


Int[(g_.+h_.*x_)^m_.*Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^s_.,x_Symbol] :=
  (g+h*x)^(m+1)*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^s/(h*(m+1)) - 
  p*r*s*(b*c-a*d)/(h*(m+1))*Int[(g+h*x)^(m+1)*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^(s-1)/((a+b*x)*(c+d*x)),x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,p,q,r,s},x] && NeQ[b*c-a*d,0] && IGtQ[s,0] && NeQ[m,-1] && EqQ[p+q,0]


Int[(g_.+h_.*x_)^m_.*Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^s_.,x_Symbol] :=
  (g+h*x)^(m+1)*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^s/(h*(m+1)) - 
  b*p*r*s/(h*(m+1))*Int[(g+h*x)^(m+1)*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^(s-1)/(a+b*x),x] - 
  d*q*r*s/(h*(m+1))*Int[(g+h*x)^(m+1)*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^(s-1)/(c+d*x),x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,p,q,r,s},x] && NeQ[b*c-a*d,0] && IGtQ[s,0] && NeQ[m,-1] && NeQ[p+q,0]


Int[1/((g_.+h_.*x_)^2*Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]),x_Symbol] :=
  b*(c+d*x)*(e*(f*(a+b*x)^p*(c+d*x)^q)^r)^(1/(p*r))/(h*p*r*(b*c-a*d)*(g+h*x))*
    ExpIntegralEi[-1/(p*r)*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]] /;
FreeQ[{a,b,c,d,e,f,g,h,p,q,r},x] && NeQ[b*c-a*d,0] && EqQ[p+q,0] && EqQ[b*g-a*h,0]


Int[Log[i_.*(j_.*(h_.*x_)^t_.)^u_.]^m_.*Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]/x_,x_Symbol] :=
  Log[i*(j*(h*x)^t)^u]^(m+1)*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]/(t*u*(m+1)) - 
  b*p*r/(t*u*(m+1))*Int[Log[i*(j*(h*x)^t)^u]^(m+1)/(a+b*x),x] - 
  d*q*r/(t*u*(m+1))*Int[Log[i*(j*(h*x)^t)^u]^(m+1)/(c+d*x),x] /;
FreeQ[{a,b,c,d,e,f,h,i,j,m,p,q,r,t,u},x] && NeQ[b*c-a*d,0] && IGtQ[m,0]


Int[Log[i_.*(j_.*(h_.*x_)^t_.)^u_.]^m_.*Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^s_./x_,x_Symbol] :=
  Defer[Int][Log[i*(j*(h*x)^t)^u]^m*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^s/x,x] /;
FreeQ[{a,b,c,d,e,f,h,i,j,m,p,q,r,s,t,u},x] && NeQ[b*c-a*d,0]


Int[u_*Log[e_.*(c_.+d_.*x_)/(a_.+b_.*x_)],x_Symbol] :=
  With[{g=Coeff[Simplify[1/(u*(a+b*x))],x,0],h=Coeff[Simplify[1/(u*(a+b*x))],x,1]},
  -(b-d*e)*PolyLog[2,(b-d*e)*(g+h*x)/(h*(a+b*x))]/(e*h*(b*c-a*d)) /;
 EqQ[g*(b-d*e)-h*(a-c*e),0]] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b*c-a*d,0] && LinearQ[Simplify[1/(u*(a+b*x))],x]


Int[u_*Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^s_.,x_Symbol] :=
  With[{g=Coeff[Simplify[1/(u*(a+b*x))],x,0],h=Coeff[Simplify[1/(u*(a+b*x))],x,1]},
  -Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^s/(b*g-a*h)*Log[-(b*c-a*d)*(g+h*x)/((d*g-c*h)*(a+b*x))] + 
  p*r*s*(b*c-a*d)/(b*g-a*h)*
    Int[Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^(s-1)/((a+b*x)*(c+d*x))*Log[-(b*c-a*d)*(g+h*x)/((d*g-c*h)*(a+b*x))],x] /;
 NeQ[b*g-a*h,0] && NeQ[d*g-c*h,0]] /;
FreeQ[{a,b,c,d,e,f,p,q,r,s},x] && NeQ[b*c-a*d,0] && IGtQ[s,0] && EqQ[p+q,0] && LinearQ[Simplify[1/(u*(a+b*x))],x]


Int[u_/Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.],x_Symbol] :=
  With[{h=Simplify[u*(a+b*x)*(c+d*x)]},
  h*Log[Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]]/(p*r*(b*c-a*d)) /;
 FreeQ[h,x]] /;
FreeQ[{a,b,c,d,e,f,p,q,r},x] && NeQ[b*c-a*d,0] && EqQ[p+q,0]


Int[u_*Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^s_.,x_Symbol] :=
  With[{h=Simplify[u*(a+b*x)*(c+d*x)]},
  h*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^(s+1)/(p*r*(s+1)*(b*c-a*d)) /;
 FreeQ[h,x]] /;
FreeQ[{a,b,c,d,e,f,p,q,r,s},x] && NeQ[b*c-a*d,0] && EqQ[p+q,0] && NeQ[s,-1]


Int[u_*Log[v_]*Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^s_.,x_Symbol] :=
  With[{g=Simplify[(v-1)*(c+d*x)/(a+b*x)],h=Simplify[u*(a+b*x)*(c+d*x)]},
  -h*PolyLog[2,-g*(a+b*x)/(c+d*x)]*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^s/(b*c-a*d) + 
  h*p*r*s*Int[PolyLog[2,-g*(a+b*x)/(c+d*x)]*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^(s-1)/((a+b*x)*(c+d*x)),x] /;
 FreeQ[{g,h},x]] /;
FreeQ[{a,b,c,d,e,f,p,q,r,s},x] && NeQ[b*c-a*d,0] && IGtQ[s,0] && EqQ[p+q,0]


Int[v_*Log[i_.*(j_.*(g_.+h_.*x_)^t_.)^u_.]*Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^s_.,x_Symbol] :=
  With[{k=Simplify[v*(a+b*x)*(c+d*x)]},
  k*Log[i*(j*(g+h*x)^t)^u]*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^(s+1)/(p*r*(s+1)*(b*c-a*d)) - 
  k*h*t*u/(p*r*(s+1)*(b*c-a*d))*Int[Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^(s+1)/(g+h*x),x] /;
 FreeQ[k,x]] /;
FreeQ[{a,b,c,d,e,f,g,h,i,j,p,q,r,s,t,u},x] && NeQ[b*c-a*d,0] && EqQ[p+q,0] && NeQ[s,-1]


Int[u_*PolyLog[n_,v_]*Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^s_.,x_Symbol] :=
  With[{g=Simplify[v*(c+d*x)/(a+b*x)],h=Simplify[u*(a+b*x)*(c+d*x)]},
  h*PolyLog[n+1,g*(a+b*x)/(c+d*x)]*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^s/(b*c-a*d) - 
  h*p*r*s*Int[PolyLog[n+1,g*(a+b*x)/(c+d*x)]*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^(s-1)/((a+b*x)*(c+d*x)),x] /;
 FreeQ[{g,h},x]] /;
FreeQ[{a,b,c,d,e,f,n,p,q,r,s},x] && NeQ[b*c-a*d,0] && IGtQ[s,0] && EqQ[p+q,0]


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^s_.,x_Symbol] :=
  (a+b*x)^(m+1)*(c+d*x)^(n+1)*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^s/((m+1)*(b*c-a*d)) - 
  p*r*s*(b*c-a*d)/((m+1)*(b*c-a*d))*Int[(a+b*x)^m*(c+d*x)^n*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^(s-1),x] /;
FreeQ[{a,b,c,d,e,f,m,n,p,q,r,s},x] && NeQ[b*c-a*d,0] && EqQ[p+q,0] && EqQ[m+n+2,0] && NeQ[m,-1] && IGtQ[s,0]


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_./Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.],x_Symbol] :=
  (a+b*x)^(m+1)*(c+d*x)^(n+1)/(p*r*(b*c-a*d)*(e*(f*(a+b*x)^p*(c+d*x)^q)^r)^((m+1)/(p*r)))*
    ExpIntegralEi[(m+1)/(p*r)*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]] /;
FreeQ[{a,b,c,d,e,f,m,n,p,q,r},x] && NeQ[b*c-a*d,0] && EqQ[p+q,0] && EqQ[m+n+2,0] && NeQ[m,-1]


Int[RFx_.*Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.],x_Symbol] :=
  p*r*Int[RFx*Log[a+b*x],x] + 
  q*r*Int[RFx*Log[c+d*x],x] - 
  (p*r*Log[a+b*x]+q*r*Log[c+d*x] - Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r])*Int[RFx,x] /;
FreeQ[{a,b,c,d,e,f,p,q,r},x] && RationalFunctionQ[RFx,x] && NeQ[b*c-a*d,0] && 
  Not[MatchQ[RFx,u_.*(a+b*x)^m_.*(c+d*x)^n_. /; IntegersQ[m,n]]]


(* Int[RFx_*Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.],x_Symbol] :=
  With[{u=IntHide[RFx,x]},  
  u*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r] - b*p*r*Int[u/(a+b*x),x] - d*q*r*Int[u/(c+d*x),x] /;
 NonsumQ[u]] /;
FreeQ[{a,b,c,d,e,f,p,q,r},x] && RationalFunctionQ[RFx,x] && NeQ[b*c-a*d,0] *)


Int[RFx_*Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^s_.,x_Symbol] :=
  With[{u=ExpandIntegrand[Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^s,RFx,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{a,b,c,d,e,f,p,q,r,s},x] && RationalFunctionQ[RFx,x] && IGtQ[s,0]


Int[RFx_*Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^s_.,x_Symbol] :=
  Defer[Int][RFx*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^s,x] /;
FreeQ[{a,b,c,d,e,f,p,q,r,s},x] && RationalFunctionQ[RFx,x]


Int[u_.*Log[e_.*(f_.*v_^p_.*w_^q_.)^r_.]^s_.,x_Symbol] :=
  Int[u*Log[e*(f*ExpandToSum[v,x]^p*ExpandToSum[w,x]^q)^r]^s,x] /;
FreeQ[{e,f,p,q,r,s},x] && LinearQ[{v,w},x] && Not[LinearMatchQ[{v,w},x]]


Int[u_.*Log[e_.*(f_.*(g_+v_/w_))^r_.]^s_.,x_Symbol] :=
  Int[u*Log[e*(f*ExpandToSum[g*w+v,x]/ExpandToSum[w,x])^r]^s,x] /;
FreeQ[{e,f,g,r,s},x] && LinearQ[{v,w},x]


(* Int[Log[g_.*(h_.*(a_.+b_.*x_)^p_.)^q_.]*Log[i_.*(j_.*(c_.+d_.*x_)^r_.)^s_.]/(e_+f_.*x_),x_Symbol] :=
  1/f*Subst[Int[Log[g*(h*Simp[-(b*e-a*f)/f+b*x/f,x]^p)^q]*Log[i*(j*Simp[-(d*e-c*f)/f+d*x/f,x]^r)^s]/x,x],x,e+f*x] /;
FreeQ[{a,b,c,d,e,f,g,h,i,j,p,q,r,s},x] *)





(* ::Subsection::Closed:: *)
(*3.3 Miscellaneous logarithms*)


Int[Log[c_.*(a_.+b_.*x_^n_)^p_.],x_Symbol] :=
  x*Log[c*(a+b*x^n)^p] -
  b*n*p*Int[x^n/(a+b*x^n),x] /;
FreeQ[{a,b,c,n,p},x]


Int[Log[c_.*v_^p_.],x_Symbol] :=
  Int[Log[c*ExpandToSum[v,x]^p],x] /;
FreeQ[{c,p},x] && BinomialQ[v,x] && Not[BinomialMatchQ[v,x]]


Int[(a_.+b_.*Log[c_.*(d_.+e_.*x_^n_)^p_.])/(f_.+g_.*x_),x_Symbol] :=
  Log[f+g*x]*(a+b*Log[c*(d+e*x^n)^p])/g - 
  b*e*n*p/g*Int[x^(n-1)*Log[f+g*x]/(d+e*x^n),x] /;
FreeQ[{a,b,c,d,e,f,g,n,p},x]


Int[(f_.+g_.*x_)^m_.*(a_.+b_.*Log[c_.*(d_.+e_.*x_^n_)^p_.]),x_Symbol] :=
  (f+g*x)^(m+1)*(a+b*Log[c*(d+e*x^n)^p])/(g*(m+1)) - 
  b*e*n*p/(g*(m+1))*Int[x^(n-1)*(f+g*x)^(m+1)/(d+e*x^n),x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && NeQ[m+1]


Int[u_^m_.*(a_.+b_.*Log[c_.*v_^p_.]),x_Symbol] :=
  Int[ExpandToSum[u,x]^m*(a+b*Log[c*ExpandToSum[v,x]^p]),x] /;
FreeQ[{a,b,c,m,p},x] && LinearQ[u,x] && BinomialQ[v,x] && Not[LinearMatchQ[u,x] && BinomialMatchQ[v,x]]


Int[ArcSin[f_.+g_.*x_]^m_.*(a_.+b_.*Log[c_.*(d_.+e_.*x_^n_)^p_.]),x_Symbol] :=
  With[{w=IntHide[ArcSin[f+g*x]^m,x]},  
  Dist[a+b*Log[c*(d+e*x^n)^p],w,x] - 
  b*e*n*p*Int[SimplifyIntegrand[x^(n-1)*w/(d+e*x^n),x],x]] /;
FreeQ[{a,b,c,d,e,f,g,n,p},x] && PositiveIntegerQ[m]


Int[(a_.+b_.*Log[c_.*(d_.+e_.*x_^2)^p_.])/(f_.+g_.*x_^2),x_Symbol] :=
  With[{u=IntHide[1/(f+g*x^2),x]},  
  u*(a+b*Log[c*(d+e*x^2)^p]) - 2*b*e*p*Int[(x*u)/(d+e*x^2),x]] /;
FreeQ[{a,b,c,d,e,f,g,p},x]


Int[(a_.+b_.*Log[c_.*(d_+e_.*x_^2)^p_.])^n_,x_Symbol] :=
  x*(a+b*Log[c*(d+e*x^2)^p])^n - 
  2*b*e*n*p*Int[x^2*(a+b*Log[c*(d+e*x^2)^p])^(n-1)/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e,p},x] && PositiveIntegerQ[n]


Int[x_^m_.*(a_.+b_.*Log[c_.*(d_+e_.*x_^2)^p_.])^n_,x_Symbol] :=
  1/2*Subst[Int[x^((m-1)/2)*(a+b*Log[c*(d+e*x)^p])^n,x],x,x^2] /;
FreeQ[{a,b,c,d,e,p},x] && PositiveIntegerQ[n] && IntegerQ[(m-1)/2]


Int[x_^m_.*(a_.+b_.*Log[c_.*(d_+e_.*x_^2)^p_.])^n_,x_Symbol] :=
  x^(m+1)*(a+b*Log[c*(d+e*x^2)^p])^n/(m+1) - 
  2*b*e*n*p/(m+1)*Int[x^(m+2)*(a+b*Log[c*(d+e*x^2)^p])^(n-1)/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e,m,p},x] && PositiveIntegerQ[n] && Not[IntegerQ[(m-1)/2]]


Int[u_*Log[v_],x_Symbol] :=
  With[{w=DerivativeDivides[v,u*(1-v),x]},
  w*PolyLog[2,Together[1-v]] /;
 Not[FalseQ[w]]]


Int[(a_.+b_.*Log[u_])*Log[v_]*w_,x_Symbol] :=
  With[{z=DerivativeDivides[v,w*(1-v),x]},
  z*(a+b*Log[u])*PolyLog[2,Together[1-v]] - 
  b*Int[SimplifyIntegrand[z*PolyLog[2,Together[1-v]]*D[u,x]/u,x],x] /;
 Not[FalseQ[z]]] /;
FreeQ[{a,b},x] && InverseFunctionFreeQ[u,x]


Int[Log[c_.*(a_+b_.*(d_.+e_.*x_)^n_)^p_.],x_Symbol] :=
  (d+e*x)*Log[c*(a+b*(d+e*x)^n)^p]/e -
  b*n*p*Int[1/(b+a*(d+e*x)^(-n)),x] /;
FreeQ[{a,b,c,d,e,p},x] && RationalQ[n] && n<0


Int[Log[c_.*(a_+b_.*(d_.+e_.*x_)^n_.)^p_.],x_Symbol] :=
  (d+e*x)*Log[c*(a+b*(d+e*x)^n)^p]/e - n*p*x +
  a*n*p*Int[1/(a+b*(d+e*x)^n),x] /;
FreeQ[{a,b,c,d,e,n,p},x] && Not[RationalQ[n] && n<0]


Int[(a_.+b_.*Log[c_.*(d_+e_./(f_.+g_.*x_))^p_.])^n_.,x_Symbol] :=
  (e+d*(f+g*x))*(a+b*Log[c*(d+e/(f+g*x))^p])^n/(d*g) - 
  b*e*n*p/(d*g)*Subst[Int[(a+b*Log[c*(d+e*x)^p])^(n-1)/x,x],x,1/(f+g*x)] /;
FreeQ[{a,b,c,d,e,f,g,p},x] && PositiveIntegerQ[n]


Int[(a_.+b_.*Log[c_.*RFx_^p_.])^n_.,x_Symbol] :=
  x*(a+b*Log[c*RFx^p])^n - 
  b*n*p*Int[SimplifyIntegrand[x*(a+b*Log[c*RFx^p])^(n-1)*D[RFx,x]/RFx,x],x] /;
FreeQ[{a,b,c,p},x] && RationalFunctionQ[RFx,x] && PositiveIntegerQ[n]


Int[(a_.+b_.*Log[c_.*RFx_^p_.])^n_./(d_.+e_.*x_),x_Symbol] :=
  Log[d+e*x]*(a+b*Log[c*RFx^p])^n/e - 
  b*n*p/e*Int[Log[d+e*x]*(a+b*Log[c*RFx^p])^(n-1)*D[RFx,x]/RFx,x] /;
FreeQ[{a,b,c,d,e,p},x] && RationalFunctionQ[RFx,x] && PositiveIntegerQ[n]


Int[(d_.+e_.*x_)^m_.*(a_.+b_.*Log[c_.*RFx_^p_.])^n_.,x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*Log[c*RFx^p])^n/(e*(m+1)) - 
  b*n*p/(e*(m+1))*Int[SimplifyIntegrand[(d+e*x)^(m+1)*(a+b*Log[c*RFx^p])^(n-1)*D[RFx,x]/RFx,x],x] /;
FreeQ[{a,b,c,d,e,m,p},x] && RationalFunctionQ[RFx,x] && PositiveIntegerQ[n] && (n==1 || IntegerQ[m]) && NeQ[m+1]


Int[Log[c_.*RFx_^n_.]/(d_+e_.*x_^2),x_Symbol] :=
  With[{u=IntHide[1/(d+e*x^2),x]},  
  u*Log[c*RFx^n] - n*Int[SimplifyIntegrand[u*D[RFx,x]/RFx,x],x]] /;
FreeQ[{c,d,e,n},x] && RationalFunctionQ[RFx,x] && Not[PolynomialQ[RFx,x]]


Int[Log[c_.*Px_^n_.]/Qx_,x_Symbol] :=
  With[{u=IntHide[1/Qx,x]},  
  u*Log[c*Px^n] - n*Int[SimplifyIntegrand[u*D[Px,x]/Px,x],x]] /;
FreeQ[{c,n},x] && QuadraticQ[{Qx,Px},x] && EqQ[D[Px/Qx,x]]


Int[RGx_*(a_.+b_.*Log[c_.*RFx_^p_.])^n_.,x_Symbol] :=
  With[{u=ExpandIntegrand[(a+b*Log[c*RFx^p])^n,RGx,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{a,b,c,p},x] && RationalFunctionQ[RFx,x] && RationalFunctionQ[RGx,x] && PositiveIntegerQ[n]


Int[RGx_*(a_.+b_.*Log[c_.*RFx_^p_.])^n_.,x_Symbol] :=
  With[{u=ExpandIntegrand[RGx*(a+b*Log[c*RFx^p])^n,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{a,b,c,p},x] && RationalFunctionQ[RFx,x] && RationalFunctionQ[RGx,x] && PositiveIntegerQ[n]


Int[RFx_*(a_.+b_.*Log[u_]),x_Symbol] :=
  With[{lst=SubstForFractionalPowerOfLinear[RFx*(a+b*Log[u]),x]},
  lst[[2]]*lst[[4]]*Subst[Int[lst[[1]],x],x,lst[[3]]^(1/lst[[2]])] /;
 Not[FalseQ[lst]]] /;
FreeQ[{a,b},x] && RationalFunctionQ[RFx,x]


Int[(f_.+g_.*x_)^m_.*Log[1+e_.*(F_^(c_.*(a_.+b_.*x_)))^n_.],x_Symbol] :=
  -(f+g*x)^m*PolyLog[2,-e*(F^(c*(a+b*x)))^n]/(b*c*n*Log[F]) + 
  g*m/(b*c*n*Log[F])*Int[(f+g*x)^(m-1)*PolyLog[2,-e*(F^(c*(a+b*x)))^n],x] /;
FreeQ[{F,a,b,c,e,f,g,n},x] && RationalQ[m] && m>0


Int[(f_.+g_.*x_)^m_.*Log[d_+e_.*(F_^(c_.*(a_.+b_.*x_)))^n_.],x_Symbol] :=
  (f+g*x)^(m+1)*Log[d+e*(F^(c*(a+b*x)))^n]/(g*(m+1)) - 
  (f+g*x)^(m+1)*Log[1+e/d*(F^(c*(a+b*x)))^n]/(g*(m+1)) + 
  Int[(f+g*x)^m*Log[1+e/d*(F^(c*(a+b*x)))^n],x] /;
FreeQ[{F,a,b,c,d,e,f,g,n},x] && RationalQ[m] && m>0 && NeQ[d-1]


Int[Log[d_.+e_.*x_+f_.*Sqrt[a_.+b_.*x_+c_.*x_^2]],x_Symbol] :=
  x*Log[d+e*x+f*Sqrt[a+b*x+c*x^2]] + 
  f^2*(b^2-4*a*c)/2*Int[x/((2*d*e-b*f^2)*(a+b*x+c*x^2)-f*(b*d-2*a*e+(2*c*d-b*e)*x)*Sqrt[a+b*x+c*x^2]),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[e^2-c*f^2]


Int[Log[d_.+e_.*x_+f_.*Sqrt[a_.+c_.*x_^2]],x_Symbol] :=
  x*Log[d+e*x+f*Sqrt[a+c*x^2]] - 
  a*c*f^2*Int[x/(d*e*(a+c*x^2)+f*(a*e-c*d*x)*Sqrt[a+c*x^2]),x] /;
FreeQ[{a,c,d,e,f},x] && EqQ[e^2-c*f^2]


Int[(g_.*x_)^m_.*Log[d_.+e_.*x_+f_.*Sqrt[a_.+b_.*x_+c_.*x_^2]],x_Symbol] :=
  (g*x)^(m+1)*Log[d+e*x+f*Sqrt[a+b*x+c*x^2]]/(g*(m+1)) + 
  f^2*(b^2-4*a*c)/(2*g*(m+1))*Int[(g*x)^(m+1)/((2*d*e-b*f^2)*(a+b*x+c*x^2)-f*(b*d-2*a*e+(2*c*d-b*e)*x)*Sqrt[a+b*x+c*x^2]),x] /;
FreeQ[{a,b,c,d,e,f,g,m},x] && EqQ[e^2-c*f^2] && NeQ[m+1] && IntegerQ[2*m]


Int[(g_.*x_)^m_.*Log[d_.+e_.*x_+f_.*Sqrt[a_.+c_.*x_^2]],x_Symbol] :=
  (g*x)^(m+1)*Log[d+e*x+f*Sqrt[a+c*x^2]]/(g*(m+1)) - 
  a*c*f^2/(g*(m+1))*Int[(g*x)^(m+1)/(d*e*(a+c*x^2)+f*(a*e-c*d*x)*Sqrt[a+c*x^2]),x] /;
FreeQ[{a,c,d,e,f,g,m},x] && EqQ[e^2-c*f^2] && NeQ[m+1] && IntegerQ[2*m]


Int[v_.*Log[d_.+e_.*x_+f_.*Sqrt[u_]],x_Symbol] :=
  Int[v*Log[d+e*x+f*Sqrt[ExpandToSum[u,x]]],x] /;
FreeQ[{d,e,f},x] && QuadraticQ[u,x] && Not[QuadraticMatchQ[u,x]] && (EqQ[v-1] || MatchQ[v,(g_.*x)^m_. /; FreeQ[{g,m},x]])


Int[Log[u_],x_Symbol] :=
  x*Log[u] - Int[SimplifyIntegrand[x*D[u,x]/u,x],x] /;
InverseFunctionFreeQ[u,x]


Int[Log[u_]/(a_.+b_.*x_),x_Symbol] :=
  Log[a+b*x]*Log[u]/b -
  1/b*Int[SimplifyIntegrand[Log[a+b*x]*D[u,x]/u,x],x] /;
FreeQ[{a,b},x] && RationalFunctionQ[D[u,x]/u,x] && (NeQ[a] || Not[BinomialQ[u,x] && EqQ[BinomialDegree[u,x]^2-1]])


Int[(a_.+b_.*x_)^m_.*Log[u_],x_Symbol] :=
  (a+b*x)^(m+1)*Log[u]/(b*(m+1)) - 
  1/(b*(m+1))*Int[SimplifyIntegrand[(a+b*x)^(m+1)*D[u,x]/u,x],x] /;
FreeQ[{a,b,m},x] && InverseFunctionFreeQ[u,x] && NeQ[m+1] (* && Not[FunctionOfQ[x^(m+1),u,x]] && FalseQ[PowerVariableExpn[u,m+1,x]] *)


Int[Log[u_]/Qx_,x_Symbol] :=
  With[{v=IntHide[1/Qx,x]},  
  v*Log[u] - Int[SimplifyIntegrand[v*D[u,x]/u,x],x]] /;
QuadraticQ[Qx,x] && InverseFunctionFreeQ[u,x]


(* Int[x_^m_.*Px_.*Log[u_],x_Symbol] :=
  With[{v=IntHide[x^m*Px,x]},  
  Dist[Log[u],v] - Int[SimplifyIntegrand[v*D[u,x]/u,x],x]] /;
FreeQ[m,x] && PolynomialQ[Px,x] && InverseFunctionFreeQ[u,x] *)


Int[u_^(a_.*x_)*Log[u_],x_Symbol] :=
  u^(a*x)/a - Int[SimplifyIntegrand[x*u^(a*x-1)*D[u,x],x],x] /;
FreeQ[a,x] && InverseFunctionFreeQ[u,x]


Int[v_*Log[u_],x_Symbol] :=
  With[{w=IntHide[v,x]},  
  Dist[Log[u],w,x] - 
  Int[SimplifyIntegrand[w*D[u,x]/u,x],x] /;
 InverseFunctionFreeQ[w,x]] /;
InverseFunctionFreeQ[u,x]


Int[Log[v_]*Log[w_],x_Symbol] :=
  x*Log[v]*Log[w] - 
  Int[SimplifyIntegrand[x*Log[w]*D[v,x]/v,x],x] - 
  Int[SimplifyIntegrand[x*Log[v]*D[w,x]/w,x],x] /;
InverseFunctionFreeQ[v,x] && InverseFunctionFreeQ[w,x]


Int[u_*Log[v_]*Log[w_],x_Symbol] :=
  With[{z=IntHide[u,x]},  
  Dist[Log[v]*Log[w],z,x] - 
  Int[SimplifyIntegrand[z*Log[w]*D[v,x]/v,x],x] - 
  Int[SimplifyIntegrand[z*Log[v]*D[w,x]/w,x],x] /;
 InverseFunctionFreeQ[z,x]] /;
InverseFunctionFreeQ[v,x] && InverseFunctionFreeQ[w,x]


Int[Log[a_.*Log[b_.*x_^n_.]^p_.],x_Symbol] :=
  x*Log[a*Log[b*x^n]^p] - 
  n*p*Int[1/Log[b*x^n],x] /;
FreeQ[{a,b,n,p},x]


Int[Log[a_.*Log[b_.*x_^n_.]^p_.]/x_,x_Symbol] :=
  Log[b*x^n]*(-p+Log[a*Log[b*x^n]^p])/n /;
FreeQ[{a,b,n,p},x]


Int[x_^m_.*Log[a_.*Log[b_.*x_^n_.]^p_.],x_Symbol] :=
  x^(m+1)*Log[a*Log[b*x^n]^p]/(m+1) - 
  n*p/(m+1)*Int[x^m/Log[b*x^n],x] /;
FreeQ[{a,b,m,n,p},x] && NeQ[m+1]


Int[(A_.+B_.*Log[c_.+d_.*x_])/Sqrt[a_+b_.*Log[c_.+d_.*x_]],x_Symbol] :=
  (b*A-a*B)/b*Int[1/Sqrt[a+b*Log[c+d*x]],x] +
  B/b*Int[Sqrt[a+b*Log[c+d*x]],x] /;
FreeQ[{a,b,c,d,A,B},x] && NeQ[b*A-a*B]


Int[f_^(a_.*Log[u_]),x_Symbol] :=
  Int[u^(a*Log[f]),x] /;
FreeQ[{a,f},x]


(* If[ShowSteps,

Int[u_/x_,x_Symbol] :=
  With[{lst=FunctionOfLog[u,x]},
  ShowStep["","Int[F[Log[a*x^n]]/x,x]","Subst[Int[F[x],x],x,Log[a*x^n]]/n",Hold[
  1/lst[[3]]*Subst[Int[lst[[1]],x],x,Log[lst[[2]]]]]] /;
 Not[FalseQ[lst]]] /;
SimplifyFlag && NonsumQ[u],

Int[u_/x_,x_Symbol] :=
  With[{lst=FunctionOfLog[u,x]},
  1/lst[[3]]*Subst[Int[lst[[1]],x],x,Log[lst[[2]]]] /;
 Not[FalseQ[lst]]] /;
NonsumQ[u]] *)


If[ShowSteps,

Int[u_,x_Symbol] :=
  With[{lst=FunctionOfLog[Cancel[x*u],x]},
  ShowStep["","Int[F[Log[a*x^n]]/x,x]","Subst[Int[F[x],x],x,Log[a*x^n]]/n",Hold[
  1/lst[[3]]*Subst[Int[lst[[1]],x],x,Log[lst[[2]]]]]] /;
 Not[FalseQ[lst]]] /;
SimplifyFlag && NonsumQ[u],

Int[u_,x_Symbol] :=
  With[{lst=FunctionOfLog[Cancel[x*u],x]},
  1/lst[[3]]*Subst[Int[lst[[1]],x],x,Log[lst[[2]]]] /;
 Not[FalseQ[lst]]] /;
NonsumQ[u]]


Int[u_.*Log[Gamma[v_]],x_Symbol] :=
  (Log[Gamma[v]]-LogGamma[v])*Int[u,x] + Int[u*LogGamma[v],x]


Int[u_.*(a_. w_+b_. w_*Log[v_]^n_.)^p_.,x_Symbol] :=
  Int[u*w^p*(a+b*Log[v]^n)^p,x] /;
FreeQ[{a,b,n},x] && IntegerQ[p]


Int[u_.*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_,x_Symbol] :=
  Defer[Int][u*(a+b*Log[c*(d*(e+f*x)^p)^q])^n,x] /;
FreeQ[{a,b,c,d,e,f,n,p,q},x] && AlgebraicFunctionQ[u,x]



