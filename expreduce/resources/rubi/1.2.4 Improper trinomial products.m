(* ::Package:: *)

(* ::Section:: *)
(*1.2.4 Improper Trinomial Product Integration Rules*)


(* ::Subsection::Closed:: *)
(*1.2.4.1 (a x^q+b x^n+c x^(2 n-q))^p*)


Int[(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  Int[((a+b+c)*x^n)^p,x] /;
FreeQ[{a,b,c,n,p},x] && EqQ[n-q] && EqQ[r-n]


Int[(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  Int[x^(p*q)*(a+b*x^(n-q)+c*x^(2*(n-q)))^p,x] /;
FreeQ[{a,b,c,n,q},x] && EqQ[r-(2*n-q)] && PosQ[n-q] && IntegerQ[p]


Int[Sqrt[a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.],x_Symbol] :=
  Sqrt[a*x^q+b*x^n+c*x^(2*n-q)]/(x^(q/2)*Sqrt[a+b*x^(n-q)+c*x^(2*(n-q))])*
    Int[x^(q/2)*Sqrt[a+b*x^(n-q)+c*x^(2*(n-q))],x] /;
FreeQ[{a,b,c,n,q},x] && EqQ[r-(2*n-q)] && PosQ[n-q]


Int[1/Sqrt[a_.*x_^2+b_.*x_^n_.+c_.*x_^r_.],x_Symbol] :=
  -2/(n-2)*Subst[Int[1/(4*a-x^2),x],x,x*(2*a+b*x^(n-2))/Sqrt[a*x^2+b*x^n+c*x^r]] /;
FreeQ[{a,b,c,n,r},x] && EqQ[r,2*n-2] && PosQ[n-2] && NeQ[b^2-4*a*c,0]


Int[1/Sqrt[a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.],x_Symbol] :=
  x^(q/2)*Sqrt[a+b*x^(n-q)+c*x^(2*(n-q))]/Sqrt[a*x^q+b*x^n+c*x^(2*n-q)]*
    Int[1/(x^(q/2)*Sqrt[a+b*x^(n-q)+c*x^(2*(n-q))]),x] /;
FreeQ[{a,b,c,n,q},x] && EqQ[r-(2*n-q)] && PosQ[n-q]


Int[(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  x*(a*x^q+b*x^n+c*x^(2*n-q))^p/(p*(2*n-q)+1) + 
  (n-q)*p/(p*(2*n-q)+1)*
    Int[x^q*(2*a+b*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^(p-1),x] /;
FreeQ[{a,b,c,n,q},x] && EqQ[r-(2*n-q)] && PosQ[n-q] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c] && RationalQ[p] && p>0 && 
  NeQ[p*(2*n-q)+1]


Int[(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  -x^(-q+1)*(b^2-2*a*c+b*c*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1)/(a*(n-q)*(p+1)*(b^2-4*a*c)) + 
  1/(a*(n-q)*(p+1)*(b^2-4*a*c))*
    Int[x^(-q)*((p*q+1)*(b^2-2*a*c)+(n-q)*(p+1)*(b^2-4*a*c)+b*c*(p*q+(n-q)*(2*p+3)+1)*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1),x] /;
FreeQ[{a,b,c,n,q},x] && EqQ[r-(2*n-q)] && PosQ[n-q] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c] && RationalQ[p] && p<-1


Int[(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  (a*x^q+b*x^n+c*x^(2*n-q))^p/(x^(p*q)*(a+b*x^(n-q)+c*x^(2*(n-q)))^p)*
    Int[x^(p*q)*(a+b*x^(n-q)+c*x^(2*(n-q)))^p,x] /;
FreeQ[{a,b,c,n,p,q},x] && EqQ[r-(2*n-q)] && PosQ[n-q] && Not[IntegerQ[p]]


Int[(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  Defer[Int][(a*x^q+b*x^n+c*x^(2*n-q))^p,x] /;
FreeQ[{a,b,c,n,p,q},x] && EqQ[r-(2*n-q)]


Int[(a_.*u_^q_.+b_.*u_^n_.+c_.*u_^r_.)^p_,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a*x^q+b*x^n+c*x^(2*n-q))^p,x],x,u] /;
FreeQ[{a,b,c,n,p,q},x] && EqQ[r-(2*n-q)] && LinearQ[u,x] && NeQ[u-x]





(* ::Subsection::Closed:: *)
(*1.2.4.2 (d x)^m (a x^q+b x^n+c x^(2 n-q))^p*)


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_.,x_Symbol] :=
  Int[x^m*((a+b+c)*x^n)^p,x] /;
FreeQ[{a,b,c,m,n,p},x] && EqQ[q-n] && EqQ[r-n]


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_.,x_Symbol] :=
  Int[x^(m+p*q)*(a+b*x^(n-q)+c*x^(2*(n-q)))^p,x] /;
FreeQ[{a,b,c,m,n,q},x] && EqQ[r-(2*n-q)] && IntegerQ[p] && PosQ[n-q]


Int[x_^m_./Sqrt[a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.],x_Symbol] :=
  -2/(n-q)*Subst[Int[1/(4*a-x^2),x],x,x^(m+1)*(2*a+b*x^(n-q))/Sqrt[a*x^q+b*x^n+c*x^r]] /;
FreeQ[{a,b,c,m,n,q,r},x] && EqQ[r,2*n-q] && PosQ[n-q] && NeQ[b^2-4*a*c,0] && EqQ[m,q/2-1]


Int[x_^m_./Sqrt[a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.],x_Symbol] :=
  x^(q/2)*Sqrt[a+b*x^(n-q)+c*x^(2*(n-q))]/Sqrt[a*x^q+b*x^n+c*x^(2*n-q)]*
    Int[x^(m-q/2)/Sqrt[a+b*x^(n-q)+c*x^(2*(n-q))],x] /;
FreeQ[{a,b,c,m,n,q},x] && EqQ[r-(2*n-q)] && PosQ[n-q] && (EqQ[m-1] && EqQ[n-3] && EqQ[q-2]  ||  
  (EqQ[m+1/2] || EqQ[m-3/2] || EqQ[m-1/2] || EqQ[m-5/2]) && EqQ[n-3] && EqQ[q-1])


Int[x_^m_./(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^(3/2),x_Symbol] :=
  -2*x^((n-1)/2)*(b+2*c*x)/((b^2-4*a*c)*Sqrt[a*x^(n-1)+b*x^n+c*x^(n+1)]) /;
FreeQ[{a,b,c,n},x] && EqQ[m-3*(n-1)/2] && EqQ[q-n+1] && EqQ[r-n-1] && NeQ[b^2-4*a*c]


Int[x_^m_./(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^(3/2),x_Symbol] :=
  x^((n-1)/2)*(4*a+2*b*x)/((b^2-4*a*c)*Sqrt[a*x^(n-1)+b*x^n+c*x^(n+1)]) /;
FreeQ[{a,b,c,n},x] && EqQ[m-(3*n-1)/2] && EqQ[q-n+1] && EqQ[r-n-1] && NeQ[b^2-4*a*c]


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  x^(m-n)*(a*x^(n-1)+b*x^n+c*x^(n+1))^(p+1)/(2*c*(p+1)) - 
  b/(2*c)*Int[x^(m-1)*(a*x^(n-1)+b*x^n+c*x^(n+1))^p,x] /;
FreeQ[{a,b,c},x] && EqQ[r-(2*n-q)] && PosQ[n-q] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p,q] && m+p*(n-1)-1==0


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  x^(m-n+q+1)*(b+2*c*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^p/(2*c*(n-q)*(2*p+1)) - 
  p*(b^2-4*a*c)/(2*c*(2*p+1))*Int[x^(m+q)*(a*x^q+b*x^n+c*x^(2*n-q))^(p-1),x] /;
FreeQ[{a,b,c},x] && EqQ[r-(2*n-q)] && PosQ[n-q] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p,q] && p>0 && m+p*q+1==n-q


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  x^(m-n+q+1)*(b*(n-q)*p+c*(m+p*q+(n-q)*(2*p-1)+1)*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^p/(c*(m+p*(2*n-q)+1)*(m+p*q+(n-q)*(2*p-1)+1)) + 
  (n-q)*p/(c*(m+p*(2*n-q)+1)*(m+p*q+(n-q)*(2*p-1)+1))*
    Int[x^(m-(n-2*q))*
      Simp[-a*b*(m+p*q-n+q+1)+(2*a*c*(m+p*q+(n-q)*(2*p-1)+1)-b^2*(m+p*q+(n-q)*(p-1)+1))*x^(n-q),x]*
      (a*x^q+b*x^n+c*x^(2*n-q))^(p-1),x] /;
FreeQ[{a,b,c},x] && EqQ[r-(2*n-q)] && PosQ[n-q] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p,q] && p>0 && m+p*q+1>n-q && m+p*(2*n-q)+1!=0 && m+p*q+(n-q)*(2*p-1)+1!=0


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  x^(m+1)*(a*x^q+b*x^n+c*x^(2*n-q))^p/(m+p*q+1) - 
  (n-q)*p/(m+p*q+1)*Int[x^(m+n)*(b+2*c*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^(p-1),x] /;
FreeQ[{a,b,c},x] && EqQ[r-(2*n-q)] && PosQ[n-q] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p,q] && p>0 && m+p*q+1<=-(n-q)+1 && NeQ[m+p*q+1]


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  x^(m+1)*(a*x^q+b*x^n+c*x^(2*n-q))^p/(m+p*(2*n-q)+1) + 
  (n-q)*p/(m+p*(2*n-q)+1)*Int[x^(m+q)*(2*a+b*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^(p-1),x] /;
FreeQ[{a,b,c},x] && EqQ[r-(2*n-q)] && PosQ[n-q] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p,q] && p>0 && m+p*q+1>-(n-q) && m+p*(2*n-q)+1!=0


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  -x^(m-q+1)*(b^2-2*a*c+b*c*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1)/(a*(n-q)*(p+1)*(b^2-4*a*c)) + 
  (2*a*c-b^2*(p+2))/(a*(p+1)*(b^2-4*a*c))*
    Int[x^(m-q)*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1),x] /;
FreeQ[{a,b,c},x] && EqQ[r-(2*n-q)] && PosQ[n-q] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p,q] && p<-1 && m+p*q+1==-(n-q)*(2*p+3)


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  -x^(m-2*n+q+1)*(2*a+b*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1)/((n-q)*(p+1)*(b^2-4*a*c)) + 
  1/((n-q)*(p+1)*(b^2-4*a*c))*
    Int[x^(m-2*n+q)*(2*a*(m+p*q-2*(n-q)+1)+b*(m+p*q+(n-q)*(2*p+1)+1)*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1),x] /;
FreeQ[{a,b,c},x] && EqQ[r-(2*n-q)] && PosQ[n-q] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p,q] && p<-1 && m+p*q+1>2*(n-q)


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  -x^(m-q+1)*(b^2-2*a*c+b*c*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1)/(a*(n-q)*(p+1)*(b^2-4*a*c)) + 
  1/(a*(n-q)*(p+1)*(b^2-4*a*c))*
    Int[x^(m-q)*
      (b^2*(m+p*q+(n-q)*(p+1)+1)-2*a*c*(m+p*q+2*(n-q)*(p+1)+1)+b*c*(m+p*q+(n-q)*(2*p+3)+1)*x^(n-q))*
      (a*x^q+b*x^n+c*x^(2*n-q))^(p+1),x] /;
FreeQ[{a,b,c},x] && EqQ[r-(2*n-q)] && PosQ[n-q] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p,q] && p<-1 && m+p*q+1<n-q


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  x^(m-n+1)*(b+2*c*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1)/((n-q)*(p+1)*(b^2-4*a*c)) - 
  1/((n-q)*(p+1)*(b^2-4*a*c))*
    Int[x^(m-n)*(b*(m+p*q-n+q+1)+2*c*(m+p*q+2*(n-q)*(p+1)+1)*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1),x] /;
FreeQ[{a,b,c},x] && EqQ[r-(2*n-q)] && PosQ[n-q] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p,q] && p<-1 && n-q<m+p*q+1<2*(n-q)


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  x^(m-2*n+q+1)*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1)/(2*c*(n-q)*(p+1)) - 
  b/(2*c)*Int[x^(m-n+q)*(a*x^q+b*x^n+c*x^(2*n-q))^p,x] /;
FreeQ[{a,b,c},x] && EqQ[r-(2*n-q)] && PosQ[n-q] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p,q] && -1<=p<0 && m+p*q+1==2*(n-q)


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  -x^(m-q+1)*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1)/(2*a*(n-q)*(p+1)) - 
  b/(2*a)*Int[x^(m+n-q)*(a*x^q+b*x^n+c*x^(2*n-q))^p,x] /;
FreeQ[{a,b,c},x] && EqQ[r-(2*n-q)] && PosQ[n-q] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p,q] && -1<=p<0 && m+p*q+1==-2*(n-q)*(p+1)


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  x^(m-2*n+q+1)*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1)/(c*(m+p*q+2*(n-q)*p+1)) - 
  1/(c*(m+p*q+2*(n-q)*p+1))*
    Int[x^(m-2*(n-q))*(a*(m+p*q-2*(n-q)+1)+b*(m+p*q+(n-q)*(p-1)+1)*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^p,x] /;
FreeQ[{a,b,c},x] && EqQ[r-(2*n-q)] && PosQ[n-q] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p,q] && -1<=p<0 && m+p*q+1>2*(n-q)


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  x^(m-q+1)*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1)/(a*(m+p*q+1)) - 
  1/(a*(m+p*q+1))*
    Int[x^(m+n-q)*(b*(m+p*q+(n-q)*(p+1)+1)+c*(m+p*q+2*(n-q)*(p+1)+1)*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^p,x] /;
FreeQ[{a,b,c},x] && EqQ[r-(2*n-q)] && PosQ[n-q] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p,q] && -1<=p<0 && m+p*q+1<0


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  (a*x^q+b*x^n+c*x^(2*n-q))^p/(x^(p*q)*(a+b*x^(n-q)+c*x^(2*(n-q)))^p)*
    Int[x^(m+p*q)*(a+b*x^(n-q)+c*x^(2*(n-q)))^p,x] /;
FreeQ[{a,b,c,m,n,p,q},x] && EqQ[r-(2*n-q)] && Not[IntegerQ[p]] && PosQ[n-q]


Int[u_^m_.*(a_.*u_^q_.+b_.*u_^n_.+c_.*u_^r_.)^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[x^m*(a*x^q+b*x^n+c*x^(2*n-q))^p,x],x,u] /;
FreeQ[{a,b,c,m,n,p,q},x] && EqQ[r-(2*n-q)] && LinearQ[u,x] && NeQ[u-x]





(* ::Subsection::Closed:: *)
(*1.2.4.3 (d+e x^(n-q)) (a x^q+b x^n+c x^(2 n-q))^p*)


Int[(A_+B_.*x_^r_.)*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^j_.)^p_.,x_Symbol] :=
  Int[x^(p*q)*(A+B*x^(n-q))*(a+b*x^(n-q)+c*x^(2*(n-q)))^p,x] /;
FreeQ[{a,b,c,A,B,n,q},x] && EqQ[r-(n-q)] && EqQ[j-(2*n-q)] && IntegerQ[p] && PosQ[n-q]


(* Int[(A_+B_.*x_^j_.)*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  Sqrt[a*x^q+b*x^n+c*x^(2*n-q)]/(x^(q/2)*Sqrt[a+b*x^(n-q)+c*x^(2*(n-q))])*
    Int[x^(q*p)*(A+B*x^(n-q))*(a+b*x^(n-q)+c*x^(2*(n-q)))^p,x] /;
FreeQ[{a,b,c,A,B,n,p,q},x] && EqQ[j-(n-q)] && EqQ[r-(2*n-q)] && PosQ[n-q] && PositiveIntegerQ[p+1/2] *)


(* Int[(A_+B_.*x_^j_.)*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  x^(q/2)*Sqrt[a+b*x^(n-q)+c*x^(2*(n-q))]/Sqrt[a*x^q+b*x^n+c*x^(2*n-q)]*
    Int[x^(q*p)*(A+B*x^(n-q))*(a+b*x^(n-q)+c*x^(2*(n-q)))^p,x] /;
FreeQ[{a,b,c,A,B,n,p,q},x] && EqQ[j-(n-q)] && EqQ[r-(2*n-q)] && PosQ[n-q] && NegativeIntegerQ[p-1/2] *)


(* Int[(A_+B_.*x_^j_.)*Sqrt[a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.],x_Symbol] :=
  Sqrt[a*x^q+b*x^n+c*x^(2*n-q)]/(x^(q/2)*Sqrt[a+b*x^(n-q)+c*x^(2*(n-q))])*
    Int[x^(q/2)*(A+B*x^(n-q))*Sqrt[a+b*x^(n-q)+c*x^(2*(n-q))],x] /;
FreeQ[{a,b,c,A,B,n,q},x] && EqQ[j-(n-q)] && EqQ[r-(2*n-q)] && PosQ[n-q] *)


Int[(A_+B_.*x_^j_.)/Sqrt[a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.],x_Symbol] :=
  x^(q/2)*Sqrt[a+b*x^(n-q)+c*x^(2*(n-q))]/Sqrt[a*x^q+b*x^n+c*x^(2*n-q)]*
    Int[(A+B*x^(n-q))/(x^(q/2)*Sqrt[a+b*x^(n-q)+c*x^(2*(n-q))]),x] /;
FreeQ[{a,b,c,A,B,n,q},x] && EqQ[j-(n-q)] && EqQ[r-(2*n-q)] && PosQ[n-q] && 
  EqQ[n-3] && EqQ[q-2]


Int[(A_+B_.*x_^r_.)*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^j_.)^p_,x_Symbol] :=
  x*(b*B*(n-q)*p+A*c*(p*q+(n-q)*(2*p+1)+1)+B*c*(p*(2*n-q)+1)*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^p/
    (c*(p*(2*n-q)+1)*(p*q+(n-q)*(2*p+1)+1)) + 
  (n-q)*p/(c*(p*(2*n-q)+1)*(p*q+(n-q)*(2*p+1)+1))*
    Int[x^q*
      (2*a*A*c*(p*q+(n-q)*(2*p+1)+1)-a*b*B*(p*q+1)+(2*a*B*c*(p*(2*n-q)+1)+A*b*c*(p*q+(n-q)*(2*p+1)+1)-b^2*B*(p*q+(n-q)*p+1))*x^(n-q))*
      (a*x^q+b*x^n+c*x^(2*n-q))^(p-1),x] /;
FreeQ[{a,b,c,A,B,n,q},x] && EqQ[r-(n-q)] && EqQ[j-(2*n-q)] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c] && RationalQ[p] && p>0 && 
  NeQ[p*(2*n-q)+1] && NeQ[p*q+(n-q)*(2*p+1)+1]


Int[(A_+B_.*x_^r_.)*(a_.*x_^q_.+c_.*x_^j_.)^p_,x_Symbol] :=
  With[{n=q+r},
  x*(A*(p*q+(n-q)*(2*p+1)+1)+B*(p*(2*n-q)+1)*x^(n-q))*(a*x^q+c*x^(2*n-q))^p/((p*(2*n-q)+1)*(p*q+(n-q)*(2*p+1)+1)) + 
  (n-q)*p/((p*(2*n-q)+1)*(p*q+(n-q)*(2*p+1)+1))*
    Int[x^q*(2*a*A*(p*q+(n-q)*(2*p+1)+1)+(2*a*B*(p*(2*n-q)+1))*x^(n-q))*(a*x^q+c*x^(2*n-q))^(p-1),x] /;
 EqQ[j-(2*n-q)] && NeQ[p*(2*n-q)+1] && NeQ[p*q+(n-q)*(2*p+1)+1]] /;
FreeQ[{a,c,A,B,q},x] && Not[IntegerQ[p]] && RationalQ[p] && p>0


Int[(A_+B_.*x_^r_.)*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^j_.)^p_,x_Symbol] :=
  -x^(-q+1)*(A*b^2-a*b*B-2*a*A*c+(A*b-2*a*B)*c*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1)/(a*(n-q)*(p+1)*(b^2-4*a*c)) + 
  1/(a*(n-q)*(p+1)*(b^2-4*a*c))*
    Int[x^(-q)*
      ((A*b^2*(p*q+(n-q)*(p+1)+1)-a*b*B*(p*q+1)-2*a*A*c*(p*q+2*(n-q)*(p+1)+1)+(p*q+(n-q)*(2*p+3)+1)*(A*b-2*a*B)*c*x^(n-q))*
      (a*x^q+b*x^n+c*x^(2*n-q))^(p+1)),x] /;
FreeQ[{a,b,c,A,B,n,q},x] && EqQ[r-(n-q)] && EqQ[j-(2*n-q)] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c] && RationalQ[p] && p<-1


Int[(A_+B_.*x_^r_.)*(a_.*x_^q_.+c_.*x_^j_.)^p_,x_Symbol] :=
  With[{n=q+r},
  -x^(-q+1)*(a*A*c+a*B*c*x^(n-q))*(a*x^q+c*x^(2*n-q))^(p+1)/(a*(n-q)*(p+1)*(2*a*c)) + 
  1/(a*(n-q)*(p+1)*(2*a*c))*
    Int[x^(-q)*((a*A*c*(p*q+2*(n-q)*(p+1)+1)+a*B*c*(p*q+(n-q)*(2*p+3)+1)*x^(n-q))*(a*x^q+c*x^(2*n-q))^(p+1)),x] /;
 EqQ[j-(2*n-q)]] /;
FreeQ[{a,c,A,B,q},x] && Not[IntegerQ[p]] && RationalQ[p] && p<-1


(* Int[(A_+B_.*x_^q_)*(a_.*x_^j_.+b_.*x_^k_.+c_.*x_^n_.)^p_,x_Symbol] :=
  (a*x^j+b*x^k+c*x^n)^p/(x^(j*p)*(a+b*x^(k-j)+c*x^(2*(k-j)))^p)*
    Int[x^(j*p)*(A+B*x^(k-j))*(a+b*x^(k-j)+c*x^(2*(k-j)))^p,x] /;
FreeQ[{a,b,c,A,B,j,k,p},x] && EqQ[q-(k-j)] && EqQ[n-(2*k-j)] && PosQ[k-j] && Not[IntegerQ[p]] *)


Int[(A_+B_.*x_^j_.)*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_.,x_Symbol] :=
  Defer[Int][(A+B*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^p,x] /;
FreeQ[{a,b,c,A,B,n,p,q},x] && EqQ[j-(n-q)] && EqQ[r-(2*n-q)]


Int[(A_+B_.*u_^j_.)*(a_.*u_^q_.+b_.*u_^n_.+c_.*u_^r_.)^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(A+B*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^p,x],x,u] /;
FreeQ[{a,b,c,A,B,n,p,q},x] && EqQ[j-(n-q)] && EqQ[r-(2*n-q)] && LinearQ[u,x] && NeQ[u-x]





(* ::Subsection::Closed:: *)
(*1.2.4.4 (f x)^m (d+e x^(n-q)) (a x^q+b x^n+c x^(2 n-q))^p*)


Int[x_^m_.*(A_+B_.*x_^r_.)*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^j_.)^p_.,x_Symbol] :=
  Int[x^(m+p*q)*(A+B*x^(n-q))*(a+b*x^(n-q)+c*x^(2*(n-q)))^p,x] /;
FreeQ[{a,b,c,A,B,m,n,q},x] && EqQ[r-(n-q)] && EqQ[j-(2*n-q)] && IntegerQ[p] && PosQ[n-q]


Int[x_^m_.*(A_+B_.*x_^r_.)*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^j_.)^p_.,x_Symbol] :=
  x^(m+1)*(A*(m+p*q+(n-q)*(2*p+1)+1)+B*(m+p*q+1)*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^p/((m+p*q+1)*(m+p*q+(n-q)*(2*p+1)+1)) + 
  (n-q)*p/((m+p*q+1)*(m+p*q+(n-q)*(2*p+1)+1))*
    Int[x^(n+m)*
      Simp[2*a*B*(m+p*q+1)-A*b*(m+p*q+(n-q)*(2*p+1)+1)+(b*B*(m+p*q+1)-2*A*c*(m+p*q+(n-q)*(2*p+1)+1))*x^(n-q),x]*
      (a*x^q+b*x^n+c*x^(2*n-q))^(p-1),x] /;
FreeQ[{a,b,c,A,B},x] && EqQ[r-(n-q)] && EqQ[j-(2*n-q)] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p,q] && p>0 && m+p*q<=-(n-q) && m+p*q+1!=0 && m+p*q+(n-q)*(2*p+1)+1!=0


Int[x_^m_.*(A_+B_.*x_^r_.)*(a_.*x_^q_.+c_.*x_^j_.)^p_.,x_Symbol] :=
  With[{n=q+r},
  x^(m+1)*(A*(m+p*q+(n-q)*(2*p+1)+1)+B*(m+p*q+1)*x^(n-q))*(a*x^q+c*x^(2*n-q))^p/((m+p*q+1)*(m+p*q+(n-q)*(2*p+1)+1)) + 
  2*(n-q)*p/((m+p*q+1)*(m+p*q+(n-q)*(2*p+1)+1))*
    Int[x^(n+m)*Simp[a*B*(m+p*q+1)-A*c*(m+p*q+(n-q)*(2*p+1)+1)*x^(n-q),x]*(a*x^q+c*x^(2*n-q))^(p-1),x] /;
 EqQ[j-(2*n-q)] && PositiveIntegerQ[n] && m+p*q<=-(n-q) && m+p*q+1!=0 && m+p*q+(n-q)*(2*p+1)+1!=0] /;
FreeQ[{a,c,A,B},x] && Not[IntegerQ[p]] && RationalQ[m,p,q] && p>0


Int[x_^m_.*(A_+B_.*x_^r_.)*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^j_.)^p_.,x_Symbol] :=
  x^(m-n+1)*(A*b-2*a*B-(b*B-2*A*c)*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1)/((n-q)*(p+1)*(b^2-4*a*c)) + 
  1/((n-q)*(p+1)*(b^2-4*a*c))*
    Int[x^(m-n)*
      Simp[(m+p*q-n+q+1)*(2*a*B-A*b)+(m+p*q+2*(n-q)*(p+1)+1)*(b*B-2*A*c)*x^(n-q),x]*
      (a*x^q+b*x^n+c*x^(2*n-q))^(p+1),x] /;
FreeQ[{a,b,c,A,B},x] && EqQ[r-(n-q)] && EqQ[j-(2*n-q)] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p,q] && p<-1 && m+p*q>n-q-1


Int[x_^m_.*(A_+B_.*x_^r_.)*(a_.*x_^q_.+c_.*x_^j_.)^p_.,x_Symbol] :=
  With[{n=q+r},
  x^(m-n+1)*(a*B-A*c*x^(n-q))*(a*x^q+c*x^(2*n-q))^(p+1)/(2*a*c*(n-q)*(p+1)) - 
  1/(2*a*c*(n-q)*(p+1))*
    Int[x^(m-n)*Simp[a*B*(m+p*q-n+q+1)-A*c*(m+p*q+(n-q)*2*(p+1)+1)*x^(n-q),x]*(a*x^q+c*x^(2*n-q))^(p+1),x] /;
 EqQ[j-(2*n-q)] && PositiveIntegerQ[n] && m+p*q>n-q-1] /;
FreeQ[{a,c,A,B},x] && Not[IntegerQ[p]] && RationalQ[m,p,q] && p<-1


Int[x_^m_.*(A_+B_.*x_^r_.)*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^j_.)^p_.,x_Symbol] :=
  x^(m+1)*(b*B*(n-q)*p+A*c*(m+p*q+(n-q)*(2*p+1)+1)+B*c*(m+p*q+2*(n-q)*p+1)*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^p/
    (c*(m+p*(2*n-q)+1)*(m+p*q+(n-q)*(2*p+1)+1)) + 
  (n-q)*p/(c*(m+p*(2*n-q)+1)*(m+p*q+(n-q)*(2*p+1)+1))*
    Int[x^(m+q)*
      Simp[2*a*A*c*(m+p*q+(n-q)*(2*p+1)+1)-a*b*B*(m+p*q+1)+
        (2*a*B*c*(m+p*q+2*(n-q)*p+1)+A*b*c*(m+p*q+(n-q)*(2*p+1)+1)-b^2*B*(m+p*q+(n-q)*p+1))*x^(n-q),x]*
      (a*x^q+b*x^n+c*x^(2*n-q))^(p-1),x] /;
FreeQ[{a,b,c,A,B},x] && EqQ[r-(n-q)] && EqQ[j-(2*n-q)] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p,q] && p>0 && m+p*q>-(n-q)-1 && m+p*(2*n-q)+1!=0 && m+p*q+(n-q)*(2*p+1)+1!=0


Int[x_^m_.*(A_+B_.*x_^r_.)*(a_.*x_^q_.+c_.*x_^j_.)^p_.,x_Symbol] :=
  With[{n=q+r},
  x^(m+1)*(A*(m+p*q+(n-q)*(2*p+1)+1)+B*(m+p*q+2*(n-q)*p+1)*x^(n-q))*(a*x^q+c*x^(2*n-q))^p/
    ((m+p*(2*n-q)+1)*(m+p*q+(n-q)*(2*p+1)+1)) + 
  (n-q)*p/((m+p*(2*n-q)+1)*(m+p*q+(n-q)*(2*p+1)+1))*
    Int[x^(m+q)*Simp[2*a*A*(m+p*q+(n-q)*(2*p+1)+1)+2*a*B*(m+p*q+2*(n-q)*p+1)*x^(n-q),x]*(a*x^q+c*x^(2*n-q))^(p-1),x] /;
 EqQ[j-(2*n-q)] && PositiveIntegerQ[n] && m+p*q>-(n-q) && m+p*q+2*(n-q)*p+1!=0 && m+p*q+(n-q)*(2*p+1)+1!=0 && m+1!=n] /;
FreeQ[{a,c,A,B},x] && Not[IntegerQ[p]] && RationalQ[m,p,q] && p>0


Int[x_^m_.*(A_+B_.*x_^r_.)*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^j_.)^p_.,x_Symbol] :=
  -x^(m-q+1)*(A*b^2-a*b*B-2*a*A*c+(A*b-2*a*B)*c*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1)/(a*(n-q)*(p+1)*(b^2-4*a*c)) + 
  1/(a*(n-q)*(p+1)*(b^2-4*a*c))*
    Int[x^(m-q)*
      Simp[A*b^2*(m+p*q+(n-q)*(p+1)+1)-a*b*B*(m+p*q+1)-2*a*A*c*(m+p*q+2*(n-q)*(p+1)+1)+
        (m+p*q+(n-q)*(2*p+3)+1)*(A*b-2*a*B)*c*x^(n-q),x]*
      (a*x^q+b*x^n+c*x^(2*n-q))^(p+1),x] /;
FreeQ[{a,b,c,A,B},x] && EqQ[r-(n-q)] && EqQ[j-(2*n-q)] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p,q] && p<-1 && m+p*q<n-q-1


Int[x_^m_.*(A_+B_.*x_^r_.)*(a_.*x_^q_.+c_.*x_^j_.)^p_.,x_Symbol] :=
  With[{n=q+r},
  -x^(m-q+1)*(A*c+B*c*x^(n-q))*(a*x^q+c*x^(2*n-q))^(p+1)/(2*a*c*(n-q)*(p+1)) + 
  1/(2*a*c*(n-q)*(p+1))*
    Int[x^(m-q)*Simp[A*c*(m+p*q+2*(n-q)*(p+1)+1)+B*(m+p*q+(n-q)*(2*p+3)+1)*c*x^(n-q),x]*(a*x^q+c*x^(2*n-q))^(p+1),x] /;
 EqQ[j-(2*n-q)] && PositiveIntegerQ[n] && m+p*q<n-q-1] /;
FreeQ[{a,c,A,B},x] && Not[IntegerQ[p]] && RationalQ[m,p,q] && p<-1


Int[x_^m_.*(A_+B_.*x_^r_.)*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^j_.)^p_.,x_Symbol] :=
  B*x^(m-n+1)*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1)/(c*(m+p*q+(n-q)*(2*p+1)+1)) - 
  1/(c*(m+p*q+(n-q)*(2*p+1)+1))*
    Int[x^(m-n+q)*
      Simp[a*B*(m+p*q-n+q+1)+(b*B*(m+p*q+(n-q)*p+1)-A*c*(m+p*q+(n-q)*(2*p+1)+1))*x^(n-q),x]*
      (a*x^q+b*x^n+c*x^(2*n-q))^p,x] /;
FreeQ[{a,b,c,A,B},x] && EqQ[r-(n-q)] && EqQ[j-(2*n-q)] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p,q] && -1<=p<0 && m+p*q>=n-q-1 && m+p*q+(n-q)*(2*p+1)+1!=0


Int[x_^m_.*(A_+B_.*x_^r_.)*(a_.*x_^q_.+c_.*x_^j_.)^p_.,x_Symbol] :=
  With[{n=q+r},
  B*x^(m-n+1)*(a*x^q+c*x^(2*n-q))^(p+1)/(c*(m+p*q+(n-q)*(2*p+1)+1)) - 
  1/(c*(m+p*q+(n-q)*(2*p+1)+1))*
    Int[x^(m-n+q)*Simp[a*B*(m+p*q-n+q+1)-A*c*(m+p*q+(n-q)*(2*p+1)+1)*x^(n-q),x]*(a*x^q+c*x^(2*n-q))^p,x] /;
 EqQ[j-(2*n-q)] && PositiveIntegerQ[n] && m+p*q>=n-q-1 && m+p*q+(n-q)*(2*p+1)+1!=0] /;
FreeQ[{a,c,A,B},x] && Not[IntegerQ[p]] && RationalQ[m,p,q] && -1<=p<0


Int[x_^m_.*(A_+B_.*x_^r_.)*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^j_.)^p_.,x_Symbol] :=
  A*x^(m-q+1)*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1)/(a*(m+p*q+1)) + 
  1/(a*(m+p*q+1))*
    Int[x^(m+n-q)*
      Simp[a*B*(m+p*q+1)-A*b*(m+p*q+(n-q)*(p+1)+1)-A*c*(m+p*q+2*(n-q)*(p+1)+1)*x^(n-q),x]*
      (a*x^q+b*x^n+c*x^(2*n-q))^p,x] /;
FreeQ[{a,b,c,A,B},x] && EqQ[r-(n-q)] && EqQ[j-(2*n-q)] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p,q] && (-1<=p<0 || m+p*q+(n-q)*(2*p+1)+1==0) && m+p*q<=-(n-q) && m+p*q+1!=0


Int[x_^m_.*(A_+B_.*x_^r_.)*(a_.*x_^q_.+c_.*x_^j_.)^p_.,x_Symbol] :=
  With[{n=q+r},
  A*x^(m-q+1)*(a*x^q+c*x^(2*n-q))^(p+1)/(a*(m+p*q+1)) + 
  1/(a*(m+p*q+1))*
    Int[x^(m+n-q)*Simp[a*B*(m+p*q+1)-A*c*(m+p*q+2*(n-q)*(p+1)+1)*x^(n-q),x]*(a*x^q+c*x^(2*n-q))^p,x] /;
 EqQ[j-(2*n-q)] && PositiveIntegerQ[n] && (-1<=p<0 || m+p*q+(n-q)*(2*p+1)+1==0) && m+p*q<=-(n-q) && m+p*q+1!=0] /;
FreeQ[{a,c,A,B},x] && Not[IntegerQ[p]] && RationalQ[m,p,q]


Int[x_^m_.*(A_+B_.*x_^j_.)/Sqrt[a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.],x_Symbol] :=
  x^(q/2)*Sqrt[a+b*x^(n-q)+c*x^(2*(n-q))]/Sqrt[a*x^q+b*x^n+c*x^(2*n-q)]*
    Int[x^(m-q/2)*(A+B*x^(n-q))/Sqrt[a+b*x^(n-q)+c*x^(2*(n-q))],x] /;
FreeQ[{a,b,c,A,B,m,n,q},x] && EqQ[j-(n-q)] && EqQ[r-(2*n-q)] && PosQ[n-q] && 
	(EqQ[m-1/2] || EqQ[m+1/2]) && EqQ[n-3] && EqQ[q-1]


(* Int[x_^m_.*(A_+B_.*x_^j_.)*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  Sqrt[a*x^q+b*x^n+c*x^(2*n-q)]/(x^(q/2)*Sqrt[a+b*x^(n-q)+c*x^(2*(n-q))])*
    Int[x^(m+q*p)*(A+B*x^(n-q))*(a+b*x^(n-q)+c*x^(2*(n-q)))^p,x] /;
FreeQ[{a,b,c,A,B,m,n,p,q},x] && EqQ[j-(n-q)] && EqQ[r-(2*n-q)] && PositiveIntegerQ[p+1/2] && PosQ[n-q] *)


(* Int[x_^m_.*(A_+B_.*x_^j_.)*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  x^(q/2)*Sqrt[a+b*x^(n-q)+c*x^(2*(n-q))]/Sqrt[a*x^q+b*x^n+c*x^(2*n-q)]*
    Int[x^(m+q*p)*(A+B*x^(n-q))*(a+b*x^(n-q)+c*x^(2*(n-q)))^p,x] /;
FreeQ[{a,b,c,A,B,m,n,p,q},x] && EqQ[j-(n-q)] && EqQ[r-(2*n-q)] && NegativeIntegerQ[p-1/2] && PosQ[n-q] *)


Int[x_^m_.*(A_+B_.*x_^q_)*(a_.*x_^j_.+b_.*x_^k_.+c_.*x_^n_.)^p_,x_Symbol] :=
  (a*x^j+b*x^k+c*x^n)^p/(x^(j*p)*(a+b*x^(k-j)+c*x^(2*(k-j)))^p)*
    Int[x^(m+j*p)*(A+B*x^(k-j))*(a+b*x^(k-j)+c*x^(2*(k-j)))^p,x] /;
FreeQ[{a,b,c,A,B,j,k,m,p},x] && EqQ[q-(k-j)] && EqQ[n-(2*k-j)] && Not[IntegerQ[p]] && PosQ[k-j]


Int[u_^m_.*(A_+B_.*u_^j_.)*(a_.*u_^q_.+b_.*u_^n_.+c_.*u_^r_.)^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[x^m*(A+B*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^p,x],x,u] /;
FreeQ[{a,b,c,A,B,m,n,p,q},x] && EqQ[j-(n-q)] && EqQ[r-(2*n-q)] && LinearQ[u,x] && NeQ[u-x]



