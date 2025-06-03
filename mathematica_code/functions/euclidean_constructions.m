(* ============= Euclidean constructions ============= *)

(*Gives three normal vectors, \
where the planes realise a triple of dihedral angles*)
RealiseThreeEuclideanPlanes[x12_, x13_, x23_] := Module[
   {v1, v2, v3temp, v33, v3},
   v1 = {1, 0, 0};
   v2 = {Cos[x12], Sin[x12], 0};
   v3temp = {Cos[x13], -Cos[x13] Cot[x12] + Cos[x23] Csc[x12], 0};
   v33 = Sqrt[1 - v3temp[[1]]^2 - v3temp[[2]]^2];
   v3 = {v3temp[[1]], v3temp[[2]], v33};
   {v1, v2, v3}];

(* Given three dihedrals, \
give the face angle at that point that is opposite the 1st dihedral an\
gle *)
FaceAngleFromTripleOfDihedrals[a_, b_, c_] :=
  FullSimplify[ArcCos[(Cos[a] + Cos[b] Cos[c])/(Sin[b] Sin[c])]];
