(* Inversions at circles (which are not Mobius transformations) *)
MobTranslateAndScaleToUnitCircAtOrigin[{cent_, rad_}] :=
  {{1, -cent}, {0, rad}};

MobInvertAtUnitCircle = {{0, 1}, {1, 0}};
MobUnitCircleToRealLine = {{I, -I}, {1, 1}};
ReflectInRealLine[z_] := Conjugate[z];

(* Maps a given circle to the real line *)
MobCircleToRealLine[{cent_, rad_}] := 
  MobUnitCircleToRealLine . 
   MobTranslateAndScaleToUnitCircAtOrigin[{cent, rad}] ;

(* Composition of two reflections *)
MobComposeReflectionInTwoCircles[{cent1_, rad1_}, {cent2_, rad2_}] := 
  Module[
   {circToReal1, circToReal2},
   circToReal1 = MobCircleToRealLine[{cent1, rad1}];
   circToReal2 = MobCircleToRealLine[{cent2, rad2}];
   Inverse[circToReal2] . Conjugate[circToReal2] . 
    Conjugate[Inverse[circToReal1]] . circToReal1
   ];

(* Mobius utilities *)
MobMatrixToMap[mat_] := Function[
   {z},
   If[z==Infinity || z==-Infinity,If[mat[[2,1]]==0,Infinity,mat[[1,1]]/mat[[2,1]]],
   If[z*mat[[2,1]]+mat[[2,2]]==0, Infinity,
   (z*mat[[1, 1]] + mat[[1, 2]])/(z*mat[[2, 1]] + mat[[2, 2]])]
   ]];

SurfaceComplexToHalfSpace[z_] := {Re[z], Im[z], 0};

HalfSpaceProjectToSurfaceComplex[p_] := p[[1]] + I*p[[2]];

MobMatrixToDiskMap[m_] := Function[{p},
   (HalfSpaceToDiskPreCooked@*SurfaceComplexToHalfSpace@*
      MobMatrixToMap[m]@*HalfSpaceProjectToSurfaceComplex@*
      DiskToHalfSpacePreCooked)[p]
   ];

MobMatrixToSurfaceR2Map[m_] := Function[{p},
   ({Re[#], Im[#]} &)[MobMatrixToMap[m][p[[1]] + p[[2]]*I]]
   ];

MobFixedPoints[m_] := Module[
   {a, b, c, d, z},
   a = m[[1, 1]];
   b = m[[1, 2]];
   c = m[[2, 1]];
   d = m[[2, 2]];
   z /. Solve[c*z^2 + (d - a) z - b == 0, z]
   ];


(* Mobius rotations *)

MobRotationAtOrigin[\[Theta]_] :=
  {{Exp[I*\[Theta]/2], 0}, {0, Exp[-I*\[Theta]/2]}};

HalfPlaneRotationAboutPoint[{x_, y_}] := Function[
   {p, \[Theta]},
   Module[
    {z, z2},
    z = p[[1]] + p[[2]]*I;
    z2 = ((x*Sin[\[Theta]/2] - y*Cos[\[Theta]/2]) z - (x^2 + y^2)*
       Sin[\[Theta]/2])/(
     Sin[\[Theta]/2] z - (x*Sin[\[Theta]/2] + y*Cos[\[Theta]/2]));
    ComplexExpand[{Re[z2], Im[z2]}]
    ]
   ];

(* Represents rotation about I (and -I) by theta *)
MobHalfPlaneRotationAboutI[\[Theta]_] :=
  {{-Cos[\[Theta]/2], -Sin[\[Theta]/2]}, {Sin[\[Theta]/
     2], -Cos[\[Theta]/2]}};

MobMoveTwoToIAndMinusI[z1_, z2_] := With[
   {b = (-I*(z1 + z2))/(z1 - z2)},
   {{(I - b)/z1, b}, {0, 1}}
   ];

MobRotateAboutTwoPoints[z1_, z2_, \[Theta]_] := Module[
   {t, r},
   t = MobMoveTwoToIAndMinusI[z1, z2];
   r = MobHalfPlaneRotationAboutI[\[Theta]];
   Inverse[t] . r . t
   ];

MobTranslateOriginToI = {{1, I}, {0, 1}};

MobRotateAtI[\[Theta]_] :=
  MobTranslateOriginToI . MobRotationAtOrigin[\[Theta]] . 
   Inverse[MobTranslateOriginToI];


(*https://math.stackexchange.com/questions/256100/how-can-i-find-the-\
points-at-which-two-circles-intersect*)
FindIntersectionOfTwoCirclesAsComplexNums[{cent1_, r1_}, {cent2_, 
    r2_}] := Module[
   {x1, x2, y1, y2, d, l, h, pts0, m},
   x1 = cent1[[1]];
   x2 = cent2[[1]];
   y1 = cent1[[2]];
   y2 = cent2[[2]];
   d = Norm[cent1 - cent2];
   l = (r1^2 - r2^2 + d^2)/(2*d);
   h = Sqrt[r1^2 - l^2];
   pts0 = {{l, h}, {l, -h}};
   m = Inverse[{{x2 - x1, y2 - y1}, {y1 - y2, x2 - x1}}/d];
   {x1, y1} + # & /@ (m . # & /@ pts0)
   ];
