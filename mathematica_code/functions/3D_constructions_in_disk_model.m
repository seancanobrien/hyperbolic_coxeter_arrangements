(* ========================================================== *)
(* UTILITIES*)
(* ========================================================== *)

(*Given a SphereCircle object, \
calculate the radius and center of the sphere that makes the plane tha\
t intersects at SphereCirc*)
SphereInfoFromCirc[SphereCircle[u_, a_]] := Module[
   {cent, rad},
   rad = Sqrt[1 - a^2]/a;
   cent = 1/a u;
   {cent, rad}
   ];

(* Inverse to the above *)
GetSphereCircFromCentRad[cent_, rad_] := Module[
   {r, u},
   r = 1/Sqrt[1 + rad^2];
   u = Normalize[cent];
   SphereCircle[u, r]
   ];

(* ========================================================== *)
(* ANALYTIC PLANES *)
(* ========================================================== *)

(* Given three intersecting SphereCirc planes, \
what is the face angle at the 1st plane *)
FaceAngleFromTripleOfPlanes[planes_] := Module[
   {a, b, c},
   a = IntersectionAngle[planes[[1]], planes[[2]]];
   b = IntersectionAngle[planes[[2]], planes[[3]]];
   c = IntersectionAngle[planes[[3]], planes[[1]]];
   FaceAngleFromTripleOfDihedrals[b, a, c]
   ];

(*Given three SphereCircles, \
compute a fourth that is perpendicular to them all*)
CircPerpToThree[SphereCircle[a1_, r1_], SphereCircle[a2_, r2_], 
   SphereCircle[a3_, r3_]] :=
  Module[
   {cent, a},
   cent = Inverse[{a1, a2, a3}] . {r1, r2, r3};
   a = 1/Sqrt[cent . cent];
   SphereCircle[cent*a, a]
   ];

FracIntersectionAngleCircCirc[SphereCircle[u1_, a1_], 
   SphereCircle[u2_, a2_]] := Module[
   {rad1, rad2, cent1, cent2},
   {cent1, rad1} = SphereInfoFromCirc[SphereCircle[u1, a1]];
   {cent2, rad2} = SphereInfoFromCirc[SphereCircle[u2, a2]];
   (rad1^2 + rad2^2 - Norm[cent1 - cent2]^2)/(2*rad1*rad2)
   ];

FracIntersectionAnglePlaneCirc[planeNorm_, SphereCircle[u_, a_]] := 
  Module[
   {circRad, circCent},
   {circCent, circRad} = SphereInfoFromCirc[SphereCircle[u, a]];
   (circCent . planeNorm)/circRad
   ];

FracIntersectionAngle[SphereCircle[u1_, a1_], 
   SphereCircle[u2_, a2_]] :=
  If[Min[{a1, a2}] > 0, 
   FracIntersectionAngleCircCirc[SphereCircle[u1, a1], 
    SphereCircle[u2, a2]],
   If[Max[{a1, a2}] == 0, Cos[VectorAngle[u1, u2]],
    If[a1 == 0, 
     FracIntersectionAnglePlaneCirc[u1, SphereCircle[u2, a2]],
     FracIntersectionAnglePlaneCirc[u2, SphereCircle[u1, a1]]]]];

IntersectionAngle[SphereCircle[u1_, a1_], SphereCircle[u2_, a2_]] := 
  ArcCos[FracIntersectionAngle[SphereCircle[u1, a1], 
    SphereCircle[u2, a2]]];

(* Construct SphereCircle that is the image of input SphereCircle unde\
r map t *)
(* This finds the image of the (Euclidean) geodesic from the origin to\
 the plane and find the resulting plane from that *)
SphereCircleFromMapGeodesicOrth[SphereCircle[u_, r_], t_] := Module[
   {ogCent, ogRad, ogPointClosestToOrigin, 
    projectedTranslatedOrigin, 
    projectedTranslatedPointClosestToOrigin, 
    projectionMatrix, translatedPlaneCorrToSphereCircCent2D, 
    translatedPlaneCorrToSphereCircRad, 
    translatedPlaneCorrToSphereCircCent3D},
    {ogCent, ogRad} = SphereInfoFromCirc[SphereCircle[u, r]];
   ogPointClosestToOrigin = ogCent - ogRad*u;
   {projectedTranslatedOrigin, 
     projectedTranslatedPointClosestToOrigin, projectionMatrix} =
    ProjectTwoPointsToDisk[t[{0, 0, 0}], t[ogPointClosestToOrigin]];
   {translatedPlaneCorrToSphereCircCent2D, 
     translatedPlaneCorrToSphereCircRad} =
    GeodesicThroughPoint2OrthogonalToGeodesicThroughBothPoints2D[
     projectedTranslatedOrigin, 
     projectedTranslatedPointClosestToOrigin];
   translatedPlaneCorrToSphereCircCent3D =
    translatedPlaneCorrToSphereCircCent2D[[1]] projectionMatrix[[1]] +
      translatedPlaneCorrToSphereCircCent2D[[2]] projectionMatrix[[2]];
   GetSphereCircFromCentRad[translatedPlaneCorrToSphereCircCent3D, 
    translatedPlaneCorrToSphereCircRad]
   ];

(* Construct SphereCircle that is the image of input SphereCircle unde\
r map t *)
(* This find the image of three points on the boundary of a plane and c\
onstructs the image of the plane from that *)
SphereCircleFromMapThreePoints[SphereCircle[u_, r_], t_] := Module[
   {threePoints, imageThreePoints},
   threePoints = ThreePointsNaive[SphereCircle[u, r]];
   imageThreePoints = t /@ threePoints;
   SphereCircleThroughPointsNaive[imageThreePoints]
   ];

(* Given a SphereCircle, \
compute the resulting SphereCircle after a tranlation by d in the posi\
tive y direction *)
(*TranslateSphereCircleInYDirection[sphereCircPlane_,d_]:=\
SphereCircleFromMapGeodesicOrth[sphereCircPlane,\
TranslatePointInYDirectionDisk[#,d]&];*)
TranslateSphereCircleInZDirection[sphereCircPlane_, d_] := 
  SphereCircleFromMapGeodesicOrth[sphereCircPlane, 
   TranslatePointInZDirectionDisk[#, d] &];

TranslateSphereCircleInZDirectionPreCooked[
   SphereCircle[{x_, y_, z_}, r_], d_] :=
  SphereCircle[{x/(
    Sign[r Cosh[d] + z Sinh[d]] Sqrt[
     1 - r^2/2 + 1/2 r^2 Cosh[2 d] + 
      z Sinh[d] (2 r Cosh[d] + z Sinh[d])]), y/(
    Sign[r Cosh[d] + z Sinh[d]] Sqrt[
     1 - r^2/2 + 1/2 r^2 Cosh[2 d] + 
      z Sinh[d] (2 r Cosh[d] + z Sinh[d])]), (2 Abs[
        r Cosh[d] + z Sinh[d]] (z Cosh[d] + r Sinh[d]) Sqrt[
       4 - 2 r^2 + 2 r^2 Cosh[2 d] + 
        4 z Sinh[d] (2 r Cosh[d] + z Sinh[d])])/(-r (-4 + r^2) Cosh[
         d] + r^3 Cosh[3 d] + 
       2 z Sinh[
         d] (2 + r^2 + 3 r^2 Cosh[2 d] + 
          2 z Sinh[d] (3 r Cosh[d] + z Sinh[d])))}, (
   2 E^d Abs[r Cosh[d] + z Sinh[d]])/
   Sqrt[(r - z)^2 + E^(4 d) (r + z)^2 - 2 E^(2 d) (-2 + r^2 + z^2)]];

ReflectAcrossMultiple[s_, listToReflectAcross_] := 
  If[Length[listToReflectAcross] == 0,
   s,
   ReflectAcrossMultiple[
    ReflectAcrossPreCooked[s, Last[listToReflectAcross]], 
    Most[listToReflectAcross]]
   ];

ReflectAcross3D[SphereCircle[u_, r_], SphereCircle[v_, s_]] := Module[
   {u2d, v2d, projectionMatrix, reflectedU2d, reflectedR},
   {u2d, v2d, projectionMatrix} = ProjectTwoPointsToDisk[u, v];
   {reflectedU2d, reflectedR} = 
    ReflectPlanarGeodesicAcrossPreCooked[{u2d, r}, {v2d, s}];
   SphereCircle[reflectedU2d . projectionMatrix, reflectedR]
   ];

(* Derived from the above with simplification *)
ReflectAcrossPreCooked[SphereCircle[{x_, y_, z_}, r_], 
   SphereCircle[{a_, b_, c_}, s_]] := SphereCircle[
   Normalize[{
      2 a r s + (1 - s^2) x - 2 (a^2 x + a b y + a c z),
      2 b r s + (1 - s^2) y - 2 (b^2 y + a b x + b c z),
      2 c r s + (1 - s^2) z - 2 (c^2 z + a c x + b c y)
      }]*
    (* Note this is different to Sign[r (1+s^2)-2 s (a x+b y+c z)] *)
    (* This is because Sign[0]=0 *)
    If[r (1 + s^2) - 2 s (a x + b y + c z) < 0, -1, 1]
   ,
   \[Sqrt]((r^2 (1 + s^2)^2 - 4 r s (1 + s^2) (a x + b y + c z) + 
        4 s^2 ((-1 + c^2) (-1 + y^2) + 2 a c x z + (-1 + 2 c^2) z^2 + 
           2 b y (a x + c z) + b^2 (-1 + 2 y^2 + z^2)))/(1 + s^4 - 
        4 r s (a x + b y + c z) - 4 r s^3 (a x + b y + c z) + 
        s^2 (2 + 4 r^2 - 4 y^2 + 8 a c x z - 4 z^2 + 
           8 b y (a x + c z) + 4 b^2 (-1 + 2 y^2 + z^2) + 
           4 c^2 (-1 + y^2 + 2 z^2))))
   ];


(* ========================================================== *)
(* NUMERIC PLANES *)
(* ========================================================== *)

NumericallyConditionSphereCircle[SphereCircle[u_, a_], 
   tol_ : 0.0001] :=
  SphereCircle[Normalize[If[Abs[#] < tol, 0, #] & /@ u], 
   If[Abs[a] < tol, 0, a]];

ReflectSphereCircleNumeric[sphereCircleToReflect_, 
   sphereCircleToReflectAcross_] := 
  NumericallyConditionSphereCircle@
   ReflectAcrossPreCooked[sphereCircleToReflect, 
    NumericallyConditionSphereCircle[sphereCircleToReflectAcross]];

ReflectAcrossMultipleNumeric[s_, listToReflectAcross_] := 
  If[Length[listToReflectAcross] == 0,
   s,
   ReflectAcrossMultipleNumeric[
    ReflectSphereCircleNumeric[s, Last[listToReflectAcross]], 
    Most[listToReflectAcross]]
   ];

SphereCirclesAreEqual[SphereCircle[u1_, r1_], SphereCircle[u2_, r2_], 
   tol_ : 0.01] :=
  If[r1 < tol && r2 < tol,
   (* If both planes are equatorial then if u1 = u2, 
   both planes are equal *)
   Norm[u1 - u2] < tol || Norm[u1 + u2] < tol,
   Norm[u1 - u2] < tol && Abs[r1 - r2] < tol];

SphereCircleIsInList[circle_, list_] := 
  AnyTrue[list, SphereCirclesAreEqual[#, circle] &];


(* ========================================================== *)
(* PLOTTING *)
(* ========================================================== *)

ParamCap[SphereCircle[u_, a_]] := Module[
   {r, cent, v, w},
   {cent, r} = SphereInfoFromCirc[SphereCircle[u, a]];
   v = GenerateOrthnormVect[-u];
   w = Cross[u, v];
   Function[{\[Theta], \[Phi]}, 
    cent - r*(u*Cos[\[Phi]] + 
        Sin[\[Phi]]*(v*Cos[\[Theta]] + w*Sin[\[Theta]]))]
   ];

(* This plots the image of a plane under R^3->R^3 transformation f *)
PlotImageOfPlane[SphereCircle[u_, a_], f_, colour_ : Orange] := 
  If[a == 0,
   Module[
    {v, w},
    v = GenerateOrthnormVect[u];
    w = Cross[u, v];
    ParametricPlot3D[
     f[r*(v*Sin[\[Theta]] + w*Cos[\[Theta]])],
     {r, 0, 1}, {\[Theta], 0, 2*Pi},
     Mesh -> None, 
     PlotStyle -> 
      Directive[colour, Opacity[0.5], Specularity[White, 30]]]
    ],
   
   ParametricPlot3D[
    f@ParamCap[SphereCircle[u, a]][\[Theta], \[Phi]],
    {\[Theta], 0, 2*Pi}, {\[Phi], 0, Pi/2 - ArcCos[a]},
    Mesh -> None, 
    PlotStyle -> 
     Directive[colour, Opacity[0.5], Specularity[White, 30]]]
   ];

(* Just plotting plane *)
PlotPlane[SphereCircle[u_, a_], colour_ : Orange] := 
  PlotImageOfPlane[SphereCircle[u, a], Identity, colour];

DrawImageOfGeodesicThroughTwoPoints[p1_, p2_, f_] := Module[
   {p12d, p22d, projectionMatrix, cent2d, rad, maxAngle, t, u, v},
   {p12d, p22d, projectionMatrix} = ProjectTwoPointsToDisk[p1, p2];
   {cent2d, rad} = GeodesicThrough2Points2D[p12d, p22d];
   u = -Normalize[cent2d];
   v = Normalize[p22d - p12d];
   maxAngle = ArcCos[(Norm[cent2d] - p12d . cent2d/Norm[cent2d])/rad];
   ParametricPlot3D[
    f[(cent2d + rad (Cos[\[Theta]]*u + Sin[\[Theta]]*v)) . 
      projectionMatrix],
    {\[Theta], -maxAngle, maxAngle}
    ]
   ];

DrawGeodesicThroughTwoPoints[p1_, p2_] := 
  DrawImageOfGeodesicThroughTwoPoints[p1, p2, Identity];
