(* Wolfram Language Package *)

(* Created by the Wolfram Workbench 10-Jun-2020 *)

BeginPackage["NumberTheory`"]



(* INITIAL UTILITIES FROM NotesAnaNT *)
SetAttributes[tex, HoldFirst]
tex[exp_] := TeXForm[HoldForm[exp]]
nc[n_] := N[n] // Chop
ht[n_] := HoldForm[n] // TraditionalForm
tf := TableForm
mf := MatrixForm
df := Defer
tr := Trace
primeQpos[n_] := If[PrimeQ[n] && n > 0, True, False]


(* Cantor Bijection Functions *) 
nNaturalToInteger::usage=
			"nNaturalToInteger[n] maps N to Z"

nIntegerToNatural::usage=
			"nIntegerToNatural[n] maps Z to N"

nNaturalToQuotient::usage=
			"nNaturalToQuotient[n] maps N to Q"

nQuotientToNatural::usage=
			"nQuotientToNatural[n] maps Q to N"


(* 3X+1 Functions *)
nCollatz::usage = 
			"nCollatz[n] gives a list of the iterates in the 3n+1 problem,
    	     starting from n. The conjecture is that this sequence always
             terminates."


(* Algebraic Number Theory Functions *)
nGaussianToIdealForm::usage =
			"nGaussianToIdealForm[z] returns a 3 element list representing 
			the Ideal Form g[a:k] as {g,a,k}"


(* Arithmetical Functions *)
nFaulhaber::usage =
			"nFaulhaber[k,n] returns the sum om the kth powers of the numbers
			<n."

nCore::usage =
			"nCore[n] returns the product of the distinct prime divisors of n"

nEulerPhi::usage = 
			"nEulerPhi[k,n] returns the sum of the k-th powers of the numbers
			<n and relatively prime to n. "

nJordanTotient::usage =
			"nJordanTotient[k,n] returns the Jordan Totient function."

nDivisors::usage = 
			"nDivisors[n,k] returns the divisors of n such that d^k/n."

nMoebiusMu::usage =
			"nMoebiusMu[k,n] vanishes if n is divisible by the (k+1)st power
			of some prime; otherwise nMoebiusMu[k,n]=1 unless the prime
			factorization of n contains the k-th powers of exactly r distinct
			primes, in which case nMoebiusMu[k,n]=(-1)^r."

nDivisorProduct::usage =
			"nDivisorProduct[n_, f_] represents the product of f[d] for all 
			d that divide n."

nPrimeProduct::usage =
			"nPrimeProduct[n_, f_] represents the product of f[p] for all 
			p that divide n."

nDirichletProduct::usage =
			"nDirichletProduct[f_,g_] returns the Dirichlet Product of the
			functions f and g : f*g."

nDirichletInverse::usage =
			"nDirichletInverse[f_] returns the function g such that (f*g)=I."
			
nDirichletPower::usage=
			"nDirichletPower[f_,k_] returns f^(k), f to the kth Dirichlet 
			power."

nDirichletRoot::usage=
			"nDirichletRoot[g_,m_] returns g^(1/m)."

nDirichletCoefficient::usage=
			"nDirichletCoefficient[fun_, m_] returns the m-th coefficient of D[f[n],n^s] where
			 fun is its corresponding Zeta expression."

nDirichletCoefficientList::usage=
			"nDirichletCoefficientList[fun_, m_] returns the first m coefficients of D[f[n],n^s] where
			 fun is its corresponding Zeta expression."

nAMComponents::usage=
			"nAMComponents[fun_] returns the multiplicative component and the 
			anti-multiplicative component of an arithmetical function in a list 
			containing {fM, fA}."

nAntiMultiplicativeComponent::usage =
			"nAntiMultiplicative Component[fun_] returns the anti-multiplicative component 
			of an arithmetical function."

nMultiplicativeComponent::usage =
			"nMultiplicative Component[fun_] returns the multiplicative component 
			of an arithmetical function."

nBellSeriesCoefficient::usage=
			"nBellSeriesCoefficient[fun_, n_] returns the value of the arithmetic function 
			which corresponds to fun. Where fun is a function of p, or Bell Series."

nLehmerD::usage=
			"nLehmerD[i_,n_] returns the largest divisor d of i for which n/d is
			 prime to d."

nLehmerProduct::usage=
			"nLehmerProduct[fun1_,fun2_] returns the Dirichlet Lehmer of the
			functions f and g : f[]g."

nLehmerM::usage=
			"nLehmerM[k_,n_] returns the k-Lehmer inverse for n."

nChebyshevTheta::usage=
			"nChebyshevTheta[x_] returns the partial sum of Log counted over the primes."

nChebyshevPsi::usage=
			"nChebyshevPsi[x_] returns the partial sum of MangoldtLambda."


(* Complex Analysis Functions *)
cPath::usage=
			"cPath[n_] returns an n-Gon."

cPlotPath::usage=
			"cPlotPath[path_ , options___] returns an n-Gon graphic."

cContourIntegral::usage=
			"cContourIntegral[expr_, vbl_, contour_] returns the contour integral."

cNContourIntegral::usage=
			"cNContourIntegral[expr_, vbl_, contour_] returns the numeric contour integral."


y::usage="Declaring y as an exported symbol in the X` context";
out::usage="Declaring out as an exported symbol in the X` context";

Begin["`Private`"]
(* Implementation of the package *)
nz[n_] := (-1)^(n - 1) Floor[n/2]
zn[n_] := Piecewise[{{2 Abs[n], n < 0}, {2 n + 1, n > 0}, {1, n == 0}}]
zq1[n_] := 
 Piecewise[{{Apply[Times, 
     Map[#[[1]]^nz[#[[2]] + 1] &, FactorInteger[n]]], n != 0}, {0, 
    n == 0}}]
zq[n_] := Piecewise[{{zq1[n], n > 0}, {-zq1[-n], n < 0}, {0, n == 0}}]
qz1[n_] := 
 Piecewise[{{Apply[Times, 
     Map[#[[1]]^(zn[#[[2]]] - 1) &, FactorInteger[n]]], n != 0}, {0, 
    n == 0}}]
qz[n_] := Piecewise[{{qz1[n], n > 0}, {-qz1[-n], n < 0}, {0, n == 0}}]
q2N[n_] := zn[qz[n]]
n2Q[n_] := zq[nz[n]]
nNaturalToInteger[n_] := nz[n]
nIntegerToNatural[n_] := zn[n]
nNaturalToQuotient[n_]:= n2Q[n]
nQuotientToNatural[n_]:= q2N[n]



nCollatz[1] := {1}
nCollatz[n_Integer] := Prepend[nCollatz[3 n + 1], n] /; OddQ[n] && n > 0
nCollatz[n_Integer] := Prepend[nCollatz[n/2], n] /; EvenQ[n] && n > 0



nGaussianToIdealForm[z_] /; IntegerQ[Re[z]] && IntegerQ[Im[z]] && Im[z]!=0 :=Module[
	{q, r, g, a, k},
	g=GCD[Re[z],Im[z]];
	q=Re[z]/g;
	r=Im[z]/g;
	a=q^2+r^2;
	k=Solve[q k == -r, k, Modulus -> a][[1, 1, 2]];
	k=If[k > (a/2), k-a, k];
	{g, a, k}
  ]



nCore[n_Integer] := Apply[Times, FactorInteger[n][[All, 1]]]

nFaulhaber[m_Integer, n_Integer] := Simplify[1/(m + 1) (BernoulliB[m + 1, n + 1] - BernoulliB[m + 1, 1])]

nEulerPhi[k_Integer, n_Integer] := DirichletConvolve[nFaulhaber[k, j], MoebiusMu[j] j^k, j, n]
nEulerPhi[0, n_Integer] := EulerPhi[n]
nEulerPhi[n_Integer] := EulerPhi[n]

nJordanTotient[k_Integer, n_Integer] := 1 /; (n == 1)
nJordanTotient[k_Integer, n_Integer] := n^k nPrimeProduct[n, (1 - 1/#^k) &] /; k>=1 && n>0
nJordanTotient[n_Integer] := EulerPhi[n] /; n>0

nDivisors[n_,k_] := Divisors[Apply[Times, Map[#[[1]]^Floor[#[[2]]/k] &, FactorInteger[n]]]]
nDivisors[n_]:= nDivisors[n,1]

nMoebiusMu[k_Integer, n_Integer] := 1 /; k >= 1 && n == 1
nMoebiusMu[k_Integer, n_Integer] := MoebiusMu[n] /; k == 1 && n > 1
nMoebiusMu[k_Integer, n_Integer] := Sum[nMoebiusMu[k - 1, n/d^k] nMoebiusMu[k - 1, n/d], {d, nDivisors[n, k]}] /; k > 1 && n > 1

nDivisorProduct[n_, f_] := Apply[Times, Map[f[#] &, Divisors[n]]]

nPrimeProduct[n_,f_] := Apply[Times, Map[f[#] &, FactorInteger[n][[All, 1]]]]

nDirichletProduct[f_, g_] := Function[a, DivisorSum[a, f[#] g[a/#] &]]
nDirichletProduct[fns_List] := Fold[nDirichletProduct, First[fns], Rest[fns]] /; Length[fns] >= 2

nDirichletInverse[f_][1] := ( 1 / f[1] ) /; f[1]!=0
nDirichletInverse[f_][n_] := -( 1 / f[1] ) (Apply[Plus, Map[f[n/#] nDirichletInverse[f][#] &, Most[Divisors[n]]]]) /; f[1]!=0

nDirichletPower[f_,0]:=Function[a, Floor[1/a]]
nDirichletPower[f_,k_Integer]:=Fold[nDirichletProduct, f, ConstantArray[f, k - 1]] /; (k >= 0)
nDirichletPower[f_,k_Integer]:=nDirichletInverse[nDirichletPower[f,-k]] /; (k < 0)
nDirichletPower[f_,k_Rational][n_]:=nDirichletRoot[nDirichletPower[f,Numerator[k]],Denominator[k]][n] /; ( k > 0)

nDirichletRoot[g_,m_][1] := g[1]
nDirichletRoot[g_,m_][n_] := 
	1/m ( g[n] - Total[Map[Apply[Times, #] &, Map[nDirichletRoot[g,m][#] &, 
	Select[Tuples[Most[Divisors[n]], m], Apply[Times, #] == n &], {2}]]] )

nDirichletCoefficient[fun_, m_] := Module[{a, f, k},
  f[x_] := fun[x];
  a[1] = Limit[f[x], x -> \[Infinity]];
  a[n_] := 
   a[n] = Limit[
     Series[n^
         x (f[x] - Sum[a[k] k^-x, {k, 1, n - 1}]), {x, \[Infinity], 
        n}] // Normal, x -> \[Infinity]];
  a[m]
  ]

nDirichletCoefficientList[fun_, m_] := Module[{a, f, k},
  f[x_] := fun[x];
  a[1] = Limit[f[x], x -> \[Infinity]];
  a[n_] := 
  a[n] = Limit[
     Series[n^
         x (f[x] - Sum[a[k] k^-x, {k, 1, n - 1}]), {x, \[Infinity], 
        n}] // Normal, x -> \[Infinity]];
  Table[{n, a[n]}, {n, 1, m}]
  ]

nAMComponents[fun_] := Module[{fM, fA},
  fM := Function[a, 
    Apply[Times, Map[fun[#[[1]]^#[[2]]] &, FactorInteger[a]]]];
  fA := nDirichletProduct[nDirichletInverse[fM], fun];
  {fM, fA}
  ]
nMultiplicativeComponent[fun_] := nAMComponents[fun][[1]]
nAntiMultiplicativeComponent[fun_] := nAMComponents[fun][[2]]

nBellSeriesCoefficient[fun_, n_] := Apply[Times, 
	Map[SeriesCoefficient[Series[fun[#[[1]]], {x, 0, #[[2]]}], #[[2]]] /. SeriesCoefficient[_, _] :> 1 &, 
	FactorInteger[n]]]

nLehmerD[i_, n_] := 0 /; Not[Divisible[n, i]]
nLehmerD[i_, n_] := 1 /; i == 1
nLehmerD[i_, n_] := Apply[Times, Map[#[[1]]^#[[2, 1]] &, Select[Map[{#, IntegerExponent[{i, n}, #]} &, 
      FactorInteger[GCD[i, n]][[All, 1]]], #[[2, 1]] == #[[2, 2]] &]]] /; Divisible[n, i]

nLehmerProduct[fn1_, fn2_] := 
 Function[a, 
  Apply[Plus, 
   Map[fn1[#[[1]]] fn2[#[[2]]] &, 
    Map[#[[1]] &, 
     Select[Map[{#, LCM[#[[1]], #[[2]]]} &, 
       Tuples[Range[a], 2]], #[[2]] == a &]]]]]

nLehmerM[k_, 1] := 1
nLehmerM[k_, n_] := 
 Apply[Times, Map[(# + 1)^k - #^k &, FactorInteger[n][[All, 2]]]]

nChebyshevTheta[x_] := Sum[Log[y], {y, Select[Range[x], PrimeQ]}]

(*nChebyshevPsi[x_] := Sum[MangoldtLambda[y], {y, x}]*) 
nChebyshevPsi[x_] := Sum[nChebyshevTheta[x^(1/y)], {y, 1, Log[2, x]}]



cPath[n_] := Table[Exp[2*I*Pi*k/n], {k, 0, n}]

cPlotPath[path_ , options___] :=
 Module[{argand = Map[{Re[#], Im[#]} &, path]}, 
  grdata = {Line[argand], {PointSize[0.03],  Map[Point, argand]}};
  Show[Graphics[grdata, AspectRatio -> 1,  Axes -> True, options]]]

cContourIntegral[expr_, vbl_, contour_] :=
 	Integrate[expr, Prepend[contour, vbl]]

cNContourIntegral[expr_, vbl_, contour_] :=
 	NIntegrate[expr, Evaluate[ Prepend[contour, vbl]]]
 	
End[]

EndPackage[]
