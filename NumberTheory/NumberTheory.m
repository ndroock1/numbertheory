(* Wolfram Language Package *)

(* Created by the Wolfram Workbench 10-Jun-2020 *)

BeginPackage["NumberTheory`"]


(* UTILITIES *)
SetAttributes[tex, HoldFirst]
tex[exp_] := TeXForm[HoldForm[exp]]
nc[n_] := N[n] // Chop
ht[n_] := HoldForm[n] // TraditionalForm
tf := TableForm
mf := MatrixForm
df := Defer
tr := Trace



(* INITIAL FROM NotesANT *)
primeQpos[n_] := If[PrimeQ[n] && n > 0, True, False]

divisorProduct[n_, fun_] := 
 Apply[Times, Map[fun[#] &, Divisors[n]]]

primeProduct[n_, fun_] := 
 Apply[Times, Map[fun[#] &, FactorInteger[n][[All, 1]]]]

jordanTotient[n_Integer?Positive, k_ : 1] := 
  DivisorSum[n, #^k*MoebiusMu[n/#] &];



(* Exported symbols added here with SymbolName::usage *) 
nNaturalToInteger::usage=
			"nNaturalToInteger[n] maps N to Z"

nIntegerToNatural::usage=
			"nIntegerToNatural[n] maps Z to N"

nNaturalToQuotient::usage=
			"nNaturalToQuotient[n] maps N to Q"

nQuotientToNatural::usage=
			"nQuotientToNatural[n] maps Q to N"

nCollatz::usage = 
			"nCollatz[n] gives a list of the iterates in the 3n+1 problem,
    	     starting from n. The conjecture is that this sequence always
             terminates."

nFaulhaber::usage =
			"nFaulhaber[k,n] returns the sum om the kth powers of the numbers
			<n"

nEulerPhi::usage = 
			"nEulerPhi[k,n] returns the sum of the kth powers of the numbers
			<n and relatively prime to n. "

nDivisors::usage = 
			"nDivisors[n,k] returns the divisors of n such that d^k/n"

nDirichletPower::usage=
			"nDirichletPower[f_,k_] returns f^(k), f to the kth Dirichlet 
			power"

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

nFaulhaber[m_Integer, n_Integer] := Simplify[1/(m + 1) (BernoulliB[m + 1, n + 1] - BernoulliB[m + 1, 1])]

nEulerPhi[k_Integer, n_Integer] := DirichletConvolve[faulhaber[k, j], MoebiusMu[j] j^k, j, n]
nEulerPhi[0, n] := EulerPhi[n]
nEulerPhi[n_Integer] := nEulerPhi[0, n]

nDivisors[n_,k_] := Divisors[Apply[Times, Map[#[[1]]^Floor[#[[2]]/k] &, FactorInteger[n]]]]
nDivisors[n_]:= nDivisors[n,1]

diriProd[fn_, gn_] := Function[a, DivisorSum[a, fn[#] gn[a/#] &]]
nDirichletPower[f_,0]:=Function[a, Floor[1/a]]
nDirichletPower[f_,k_]:=Fold[diriProd, f, ConstantArray[f, k - 1]]
End[]

EndPackage[]
