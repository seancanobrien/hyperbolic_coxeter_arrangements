(* ============= Isometries and metrics in Disk Model ============= *)

DistanceInDisk[u_, v_] := With[
   {del = 2 Norm[u - v]^2/((1 - Norm[u]^2) (1 - Norm[v]^2))},
   ArcCosh[1 + del]];

TranslatePointInZDirectionDisk[{x_, y_, z_}, d_] := 
  With[{normVec = Norm[{x, y, z}]},
   {(4 E^d x)/(
    1 + normVec^2 - 2 E^d (-1 + normVec^2) - 2 z + 
     E^(2 d) (1 + normVec^2 + 2 z)), (4 E^d y)/(
    1 + normVec^2 - 2 E^d (-1 + normVec^2) - 2 z + 
     E^(2 d) (1 + normVec^2 + 2 z)), -((
     1 + normVec^2 - 2 z - E^(2 d) (1 + normVec^2 + 2 z))/(
     1 + normVec^2 - 2 E^d (-1 + normVec^2) - 2 z + 
      E^(2 d) (1 + normVec^2 + 2 z)))}
   ];

(* ============= Isometries and metrics in Half Space Model ============= \
*)

DistanceInHalfSpace[u_, v_, imaginaryAxis_ : {0, 0, 1}] := Module[
   {imagU, imagV},
   imagU = u . imaginaryAxis;
   imagV = v . imaginaryAxis;
   2 ArcSinh[Norm[u - v]/(2 Sqrt[imagU imagV])]];

TranslatePointInImaginaryDirectionHalfSpace[x_, d_] := Exp[d] x;


(* ============= Moving between models of Hyperbolic space ============= \
 *)

HalfPlaneToDisk[x_] := Module[
   {zDisk, zHalfSpace},
   zHalfSpace = x[[1]] + I * x[[2]];
   zDisk = (I*zHalfSpace + 1)/(zHalfSpace + I);
   {Re[zDisk], Im[zDisk]}
];

DiskToHalfPlane[x_] := Module[
   {zDisk, zHalfSpace},
   zDisk = x[[1]] + I * x[[2]];
   zHalfSpace = (-I*zDisk + 1)/(zDisk - I);
   {Re[zHalfSpace], Im[zHalfSpace]}
];

DiskToHalfSpace[x_, imaginaryAxis_ : {0, 0, 1}] := Module[
   {imaginaryPart, realVector, zDisk, zHalfSpace},
   imaginaryPart = x . imaginaryAxis;
   realVector = x - imaginaryPart * imaginaryAxis;
   zDisk = imaginaryPart * I + Norm[realVector];
   zHalfSpace = (-I*zDisk + 1)/(zDisk - I);
   Im[zHalfSpace]*imaginaryAxis + Re[zHalfSpace]*Normalize[realVector]
    ];
(* Get this from:
Simplify@ComplexExpand@DiskToHalfSpace[{x,y,z}]
*)

(* Before I changed to z>0 being the half space *)
(*DiskToHalfSpacePreCooked[{x_,y_,z_}]:={(2 x)/(x^2+(-1+y)^2+z^2),-((\
-1+x^2+y^2+z^2)/(1+x^2-2 y+y^2+z^2)),(2 z)/(x^2+(-1+y)^2+z^2)};*)
DiskToHalfSpacePreCooked[{x_, y_, z_}] := {(2 x)/(
   x^2 + y^2 + (-1 + z)^2), (2 y)/(
   x^2 + y^2 + (-1 + z)^2), -((-1 + x^2 + y^2 + z^2)/(
    1 + x^2 + y^2 - 2 z + z^2))};

HalfSpaceToDisk[x_, imaginaryAxis_ : {0, 0, 1}] := Module[
   {imaginaryPart, realVector, zDisk, zHalfSpace},
   imaginaryPart = x . imaginaryAxis;
   realVector = x - imaginaryPart * imaginaryAxis;
   zHalfSpace = imaginaryPart * I + Norm[realVector];
   zDisk = (I*zHalfSpace + 1)/(zHalfSpace + I);
   Im[zDisk]*imaginaryAxis + Re[zDisk]*Normalize[realVector]
   ];

(*Get this from:
Simplify@ComplexExpand@HalfSpaceToDisk[{x,y,z}]
*)
(* Before I changed to z>0 being the half space *)
(*HalfSpaceToDiskPreCooked[{x_,y_,z_}]:={(2 x)/(x^2+(1+y)^2+z^2),(-1+\
x^2+y^2+z^2)/(1+x^2+2 y+y^2+z^2),(2 z)/(x^2+(1+y)^2+z^2)};*)
HalfSpaceToDiskPreCooked[{x_, y_, z_}] := {(2 x)/(
   x^2 + y^2 + (1 + z)^2), (2 y)/(
   x^2 + y^2 + (1 + z)^2), (-1 + x^2 + y^2 + z^2)/(
   1 + x^2 + y^2 + 2 z + z^2)};

(*Given a plane corresponding to a spherecircle in the disk model, \
what is the corresponding hemisphere in the half space Model*)
(*Outputs {centreOfHemisphereOnRealPlane,HemisphereRadius}*)
SphereCircleToCentreRadInHalfSpace[SphereCircle[u_, a_], 
   imaginaryAxis_ : {0, 0, 1}] := Module[
   {capRad, capCent, pointClosestToOriginDisk, 
    pointClosestToOriginHalfSpace, imaginaryPart, realVector, 
    realPart, realHemisphereCentre, hemisphereRadius},
   {capCent, capRad} = SphereInfoFromCirc[SphereCircle[u, a]];
   pointClosestToOriginDisk = capCent - capRad*u;
   pointClosestToOriginHalfSpace = 
    DiskToHalfSpacePreCooked[pointClosestToOriginDisk];
   imaginaryPart = pointClosestToOriginHalfSpace . imaginaryAxis;
   realVector = 
    pointClosestToOriginHalfSpace - imaginaryPart * imaginaryAxis;
   realPart = Norm[realVector];
   realHemisphereCentre = (
    realPart (1 + realPart^2 + imaginaryPart^2))/(
    1 + realPart^2 - imaginaryPart^2);
   hemisphereRadius = 
    Sqrt[(4 realPart^2 imaginaryPart^4)/(1 + realPart^2 - 
         imaginaryPart^2)^2 + imaginaryPart^2];
   {realHemisphereCentre * Normalize[realVector], hemisphereRadius}
   ];

(*Derived from above with extensive simplification *)
(*SphereCircleToCentreRadInHalfSpacePreCooked[SphereCircle[{x_,y_,z_},\
r_]]:={{x/(r-y),0,z/(r-y)},Sqrt[(1-r^2)/(r-y)^2]};*)
SphereCircleToCentreRadInHalfSpacePreCooked[
   SphereCircle[{x_, y_, z_}, r_]] := {{x/(r - z), y/(r - z), 0}, 
   Sqrt[(1 - r^2)/(r - z)^2]};

KleinToDisk[p_] := With[
   {s = Norm[p]},
   p/(1 + Sqrt[1 - s^2])];

KleinToDiskCapped[p_] := With[
   {s = Norm[p]},
      If[s>0.999999999,
         0*p,
         p/(1 + Sqrt[1 - s^2])]
   ];


DiskToKlein[p_] := With[
  {u = Norm[p]},
  2/(1 + u^2) * p
  ]
