TwoPointsFromPlanarGeodesic[{u_, a_}] := With[
   {v = {-u[[2]], u[[1]]}},
   {a*u + Sqrt[1 - a^2] v, a*u - Sqrt[1 - a^2]*v}
   ];

PlanarGeodesicInfo[{u_, a_}] := Module[
   {cent, rad},
   rad = Sqrt[1 - a^2]/a;
   cent = 1/a u;
   {cent, rad}];

GetPlanarGeodesicFromCentRad[cent_, rad_] := Module[
   {r, u},
   r = 1/Sqrt[1 + rad^2];
   u = Normalize[cent];
   {u, r}
   ];

ReflectInPlanarGeodesic[x_,{u_,r_}] :=
  If[r == 0, Function[# - 2 (# . u) u][x],
   With[{cent = 1/r u, R = Sqrt[1/r^2 - 1]}, 
    Function[cent + R^2/(# - cent) . (# - cent) (# - cent)][x]]];

ReflectInMultiplePlanarGeodesic[s_, listToReflectAcross_] := 
  If[Length[listToReflectAcross] == 0,
   s,
   ReflectInMultiplePlanarGeodesic[
    ReflectInPlanarGeodesic[s, Last[listToReflectAcross]], 
    Most[listToReflectAcross]]
   ];


ReflectInPlanarGeodesicNaive[{u_, a_}] := Module[
   {cent, rad},
   {cent, rad} = PlanarGeodesicInfo[{u, a}];
   cent + rad^2/(# - cent) . (# - cent) (# - cent) &
   ];

PlanarGeodesicFromMapTwoPoints[{u_, a_}, t_] := 
  GetPlanarGeodesicFromCentRad @@ (GeodesicThrough2Points2D @@ (t /@ 
       TwoPointsFromPlanarGeodesic[{u, a}]));

(*ReflectPlanarGeodesicAcross[geodesicToReflect_,\
geodesicToReflectAcross_]:=PlanarGeodesicFromMapGeodesicOrth[\
geodesicToReflect,ReflectInPlanarGeodesicNaive[\
geodesicToReflectAcross]];*)
ReflectPlanarGeodesicAcross[geodesicToReflect_, 
   geodesicToReflectAcross_] := 
  PlanarGeodesicFromMapTwoPoints[geodesicToReflect, 
   ReflectInPlanarGeodesicNaive[geodesicToReflectAcross]];

ReflectPlanarGeodesicAcrossPreCooked[{{x_, y_}, r_}, {{a_, b_}, s_}] :=
  {
   Normalize[{
      (2*a*r*s  - 2*a*b*y - x + 2*b^2*x - s^2*x ),
      (2*b*r*s - 2*a*b*x + y - 2*b^2*y - s^2*y)
      }] * 
    (* Note this is different to Sign[r + r*s^2 - 2*a*s*x - 2*b*s*y] *)
    (* This is because Sign[0]=0 *)
     If[r + r*s^2 - 2*a*s*x - 2*b*s*y < 0, -1, 1],
   1/Sqrt[(1 + s^4 - 4*r*s*(a*x + b*y) - 4*r*s^3*(a*x + b*y) + 
                 s^2*(2 + 4*r^2 + 8*a*b*x*y - 4*y^2 + b^2*(-4 + 8*y^2)))/
              (r^2*(1 + s^2)^2 - 4*r*s*(1 + s^2)*(a*x + b*y) + 
                 4*s^2*(1 + 2*a*b*x*y - y^2 + b^2*(-1 + 2*y^2)))]
   };



(* ============= Constructions in 2D Disk model ============= *)

(*Given two 2D points inside disk, \
gives center and radius of geodesic going through those two points *)
GeodesicThrough2Points2D[{a1_, a2_}, {b1_, b2_}] :=
  {{((1 + a1^2) b2 + a2^2 b2 - a2 (1 + b1^2 + b2^2))/(-2 a2 b1 + 
     2 a1 b2), (b1 + a1^2 b1 + a2^2 b1 - a1 (1 + b1^2 + b2^2))/(
    2 a2 b1 - 2 a1 b2)}, 
   1/2 \[Sqrt](1/(a2 b1 - a1 b2)^2 ((a1 - b1)^2 + (a2 - b2)^2) (1 - 
         2 a1 b1 - 2 a2 b2 + a1^2 (b1^2 + b2^2) + a2^2 (b1^2 + b2^2)))};
GeodesicThroughPointOrthogonalToOtherGeodeodesic2D[{pointx_, 
    pointy_}, {{geodesicCentrex_, geodesicCentrey_}, 
    geodesicRadius_}] :=
  With[
   {xp = pointx,
    yp = pointy,
    xc = geodesicCentrex,
    yc = geodesicCentrey,
    rc = geodesicRadius},
   {{((-1 + rc^2 - xc^2) yp + yc (1 + xp^2 - yc yp + yp^2))/(
     2 xp yc - 2 xc yp), (
     xc^2 xp + xp (1 - rc^2 + yc^2) - xc (1 + xp^2 + yp^2))/(
     2 xp yc - 2 xc yp)}, 
    1/2 \[Sqrt](-4 + (-xc^2 xp + xp (-1 + rc^2 - yc^2) + 
          xc (1 + xp^2 + yp^2))^2/(xp yc - 
          xc yp)^2 + ((-1 + rc^2 - xc^2) yp + 
          yc (1 + xp^2 - yc yp + yp^2))^2/(xp yc - xc yp)^2)}
   ];

GeodesicThroughPoint2OrthogonalToGeodesicThroughBothPoints2D[point1_, 
   point2_] :=
  GeodesicThroughPointOrthogonalToOtherGeodeodesic2D[point2, 
   GeodesicThrough2Points2D[point1, point2]];

(*Project two coordinates to the disk that contains the origin and tho\
se two coordinates*)
ProjectTwoPointsToDisk[p1_, p2_] := Module[
   {planeNormal, planeEquation, basis1, basis2, projectionMatrix, 
    p1Projected, p2Projected},
   (*Compute the normal vector of the plane through p1,p2,
   and the origin*)
   planeNormal = Cross[p1, p2];
   (*Create an orthonormal basis for the plane*)
   basis1 = Normalize[p1];
   basis2 = Normalize[Cross[planeNormal, basis1]];
   (*Create the projection matrix to the plane*)
   projectionMatrix = {basis1, basis2};
   (*Project p1 and p2 into the plane's local coordinates*)
   p1Projected = projectionMatrix . p1;
   p2Projected = projectionMatrix . p2;
   (*Return the projected points in 2D*)
   {p1Projected, p2Projected, projectionMatrix}];

(* ========================================================== *)
(* NUMERIC *)
(* ========================================================== *)

NumericallyConditionPlanarGeodesic[{u_, a_}, 
   tol_ : 0.0001] :=
  {Normalize[If[Abs[#] < tol, 0, #] & /@ u], 
   If[Abs[a] < tol, 0, a]};

PlanarGeodesicsAreEqual[{u1_, r1_}, {u2_, r2_}, 
   tol_ : 0.01] :=
  If[r1 < tol && r2 < tol,
   (* If both planes are equatorial then if u1 = u2, 
   both planes are equal *)
   Norm[u1 - u2] < tol || Norm[u1 + u2] < tol,
   Norm[u1 - u2] < tol && Abs[r1 - r2] < tol];

ReflectPlanarGeodesicNumeric[planarGeodesicToReflect_, 
   planarGeodesicToReflectAcross_] := 
  NumericallyConditionPlanarGeodesic@
    ReflectPlanarGeodesicAcrossPreCooked[planarGeodesicToReflect,
    NumericallyConditionPlanarGeodesic[planarGeodesicToReflectAcross]];

ReflectAcrossMultiplePlanarGeodesicNumeric[s_, listToReflectAcross_] := 
  If[Length[listToReflectAcross] == 0,
   s,
   ReflectAcrossMultiplePlanarGeodesicNumeric[
    ReflectPlanarGeodesicNumeric[s, Last[listToReflectAcross]], 
    Most[listToReflectAcross]]
   ];

(* ========================================================== *)
(* PLOTTING *)
(* ========================================================== *)

PlotImageOfPlanarGeodesic[{u_, a_}, f_, colour_ : Black] := 
  If[a == 0,
   Module[
    {v},
    v = Normalize[{u[[2]],-u[[1]]}];
    ParametricPlot[
     f[r*v],
     {r, -1, 1},
     PlotStyle ->
     {Directive[colour], Thickness[0.002]}
    ]
   ],

   ParametricPlot[
    f@ParamCap2D[{u, a}][\[Theta]],
    {\[Theta], -Pi/2 + ArcCos[a], Pi/2 - ArcCos[a]},
    Mesh -> None,
    PlotStyle ->
     {Directive[colour], Thickness[0.002]}
   ]];

PlotPlanarGeodesic[{u_, a_}, colour_ : Black] :=
   PlotImageOfPlanarGeodesic[{u, a}, Identity, colour];

ParamCap2D[{u_, a_}] := Module[
   {r, cent, v, w},
   {cent, r} = PlanarGeodesicInfo[{u, a}];
   v = Normalize[{u[[2]],-u[[1]]}];
   Function[\[Theta], 
    cent - r*(v*Sin[\[Theta]] + u*Cos[\[Theta]])]
   ];
