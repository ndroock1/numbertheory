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

faulhaber[m_, n_] := 
 Simplify[1/(m + 1) (BernoulliB[m + 1, n + 1] - BernoulliB[m + 1, 1])]

divisorProduct[n_, fun_] := 
 Apply[Times, Map[fun[#] &, Divisors[n]]]

primeProduct[n_, fun_] := 
 Apply[Times, Map[fun[#] &, FactorInteger[n][[All, 1]]]]

jordanTotient[n_Integer?Positive, k_ : 1] := 
  DivisorSum[n, #^k*MoebiusMu[n/#] &];

eulerPhi[k_, n_] := 
 DirichletConvolve[faulhaber[k, j], MoebiusMu[j] j^k, j, n]
eulerPhi[0, n] := EulerPhi[n]
eulerPhi[n_] := eulerPhi[0, n]



(* Exported symbols added here with SymbolName::usage *) 



Begin["`Private`"]
(* Implementation of the package *)


End[]

EndPackage[]
