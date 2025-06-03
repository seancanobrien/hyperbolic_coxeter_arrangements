(*You give the order of each pairing and output is relevant Pi/m_\
ij matrix*)
MakeAngleMatrixFromIncedence[incedence_] := Module[
   {upper, result},
   upper = UpperTriangularize[incedence];
   result = 
    MapIndexed[If[#2[[1]] == #2[[2]], Pi, If[# != 0, Pi/#, 0]] &, 
     upper, {2}];
   result + Transpose[result] - DiagonalMatrix[Diagonal[result]]];

AllTuplesUpTo[list_, n_] := Flatten[Table[Tuples[list, k], {k, n}], 1];

NonRepeatingTuplesIndices[listLength_, n_] := Module[{extend, list},
   list = Range[listLength];
   extend[seq_] := 
    Select[Flatten[Outer[Append, {seq}, list, 1], 1], 
     Length[#] == 1 || #[[-1]] =!= #[[-2]] &];
   Flatten[FoldList[Flatten[extend /@ #, 1] &, {{}}, Range[n]], 1]];

NonRepeatingTuples[list_, n_] := 
  list[[#]] & /@ NonRepeatingTuplesIndices[Length[list], n];

(* Like DeleteDuplicates but if there are two that are equal, \
they are both deleted *)
RemovePairs[list_, f_] := 
 Module[{pairs, toRemove},(*Find all pairs (x,y) where f(x,y) is True*)
  pairs = Select[Subsets[list, {2}], Apply[f]];
  (*Flatten the pairs to get a list of elements to remove*)
  toRemove = Flatten[pairs];
  (*Remove occurrences of these elements from the list*)
  DeleteCases[list, Alternatives @@ toRemove]]
