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



Begin["`Private`"]
(* Implementation of the package *)

nCollatz[1] := {1}
nCollatz[n_Integer]  := Prepend[nCollatz[3 n + 1], n] /; OddQ[n] && n > 0
nCollatz[n_Integer] := Prepend[nCollatz[n/2], n] /; EvenQ[n] && n > 0

nFaulhaber[m_, n_] := Simplify[1/(m + 1) (BernoulliB[m + 1, n + 1] - BernoulliB[m + 1, 1])]

nEulerPhi[k_Integer, n_Integer] := DirichletConvolve[faulhaber[k, j], MoebiusMu[j] j^k, j, n]
nEulerPhi[0, n] := EulerPhi[n]
nEulerPhi[n_Integer] := nEulerPhi[0, n]

End[]

EndPackage[]
