(* ============= Jim's code ============= *)
Unprotect[SphereCircle];
DeclareKnownSymbols[{"SphereCircle"}];
(* Small bug fix by extracting GenerateOrthnormVect (and fixing it in t\
he case of ReflectAcross) *)
GenerateOrthnormVect[x_] := 
  Normalize@
   Cross[x, If[Abs[x . {0, 0, 1}] >= 0.9, {1, 0, 0}, {0, 0, 1}]];
GenerateOrthnormVectNaive[x_] := Normalize@Cross[x, {0, 0, 1}];

DrawCircle[SphereCircle[u_, r_], rad_ : 1] :=
 With[{v = 
    Normalize@
     Cross[u, If[Abs[u . {0, 0, 1}] >= 0.6, {1, 0, 0}, {0, 0, 1}]]},
  With[{w = Cross[u, v]},
   Line@Table[
     rad*(r u + 
        Sqrt[1 - r^2] (v Cos[\[Theta]] + w Sin[\[Theta]])), {\[Theta],
       0, 2 Pi, Pi/100}]
   ]]
IntersectionPoint[SphereCircle[u1_, r1_], SphereCircle[u2_, r2_]] :=
 With[{s = u1 . u2, k = Normalize@Cross[u1, u2]},
  With[{j = Cross[k, u1], t = (r2 - r1 s)/Sqrt[1 - s^2]},
   r1 u1 + t j + Sqrt[1 - r1^2 - t^2] k
   ]]
IntersectionAngle[SphereCircle[u1_, r1_], SphereCircle[u2_, r2_]] :=
 With[{p = 
    IntersectionPoint[SphereCircle[u1, r1], SphereCircle[u2, r2]]},
  VectorAngle[Cross[u1, p], Cross[u2, p]]
  ]
SphereCircleThroughPoints[{p_, q_, r_}] := 
  With[{u = Re /@ Normalize@Cross[r - q, q - p]},
   If[u . p > 0, SphereCircle[u, u . p], SphereCircle[-u, -u . p]]
   ];
SphereCircleThroughPointsNaive[{p_, q_, r_}] := 
  With[{u = Normalize@Cross[r - q, q - p]},
   SphereCircle[-u, -u . p]
   ];
ThreePoints[SphereCircle[u_, r_]] := With[{v = GenerateOrthnormVect[u]},
   With[{w = Cross[u, v]},
    {r u + Re[Sqrt[1 - r^2]] v, r u + Re[Sqrt[1 - r^2]] w, 
     r u - Re[Sqrt[1 - r^2]] v}
    ]];

ThreePointsNaive[SphereCircle[u_, r_]] := 
  With[{v = GenerateOrthnormVectNaive[u]},
   With[{w = Cross[u, v]},
    {r u + Sqrt[1 - r^2] v, r u + Sqrt[1 - r^2] w, 
     r u - Sqrt[1 - r^2] v}
    ]];

H3Reflection[SphereCircle[u_, r_]] := 
  If[r == 0, Function[# - 2 (# . u) u],
   With[{cent = 1/r u, R = Sqrt[1/r^2 - 1]}, 
    Function[cent + R^2/(# - cent) . (# - cent) (# - cent)]]];

(*H3ReflectionMultiple[tuple_]:=If[Length[tuple]==0,
Identity,
H3Reflection[First[tuple]]@H3ReflectionMultiple[Rest[tuple]]
];
*)

H3ReflectionMultiple[tuple_] := 
 Fold[Function[{f, g}, g@*f], Identity, H3Reflection /@ tuple]

(*Order that functions are called is same order as they occur in tuple\
*)
(* Fold[Function[{f,g},g@*f],Identity,f/@{a,b,c}] ==f[c]@*f[b]@*f[a] *)
ReflectAcrossMultiple[s_, listToReflectAcross_] := 
  If[Length[listToReflectAcross] == 0,
   s,
   ReflectAcrossMultiple[ReflectAcross[s, Last[listToReflectAcross]], 
    Most[listToReflectAcross]]
   ];

H3ReflectionNaive[SphereCircle[u_, r_]] := 
  With[{cent = Re[1/r] u, R = Re[Sqrt[1/r^2 - 1]]}, 
   Function[cent + R^2/(# - cent) . (# - cent) (# - cent)]];

ReflectAcross[spheretoreflect_, sphereofreflection_] := 
  With[{F = H3Reflection[sphereofreflection]},
   SphereCircleThroughPoints[F /@ ThreePoints[spheretoreflect]]];

Protect[SphereCircle];
