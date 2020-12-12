(* Wolfram Language Package *)

BeginPackage["TestPack`"]
(* Exported symbols added here with SymbolName::usage *)  

tColl::usage = 
			"tColl[n] gives a list of the iterates in the 3n+1 problem,
    	     starting from n. The conjecture is that this sequence always
             terminates."


Begin["`Private`"] (* Begin Private Context *) 
tColl[1] := {1}
tColl[n_Integer] := Prepend[tColl[3 n + 1], n] /; OddQ[n] && n > 0
tColl[n_Integer] := Prepend[tColl[n/2], n] /; EvenQ[n] && n > 0
End[] (* End Private Context *)

EndPackage[]