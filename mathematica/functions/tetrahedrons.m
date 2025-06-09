(* ========================================================== *)
(* ANALYTIC CONSTRUCTIONS *)
(* ========================================================== *)

(* Given four spherecircs that describe a tetrahedron in disk model, \
what are the coordinates of the corners in the disk model *)
TetrahedronVertsInSphereCircs[sphereCircles_] := Module[
   {planes, kleinVerts},
   (* Transform of SphereCircle to corr. 
   plane in Klein model is very simple! *)
   planes = {#[[1]], #[[2]]} & /@ sphereCircles;
   kleinVerts = TetrahedronVertsInEuclideanPlanes[planes];
   KleinToDisk /@ kleinVerts
   ];

TetrahedronVertsInKlein[sphereCircles_] := Module[
   {planes, kleinVerts},
   (* Transform of SphereCircle to corr. 
   plane in Klein model is very simple! *)
   planes = {#[[1]], #[[2]]} & /@ sphereCircles;
   TetrahedronVertsInEuclideanPlanes[planes]
   ];

(*Given a plane described by SphereCirc, \
return a function that returns true if a tetrahedron is entirely conta\
ined in
the half space that contains the origin*)
TetrahedronTouchingAndInsidePlane[sphereCirc_, tol_ : 0.001] := 
  If[sphereCirc[[2]] == 0,
   Function[tet,
    With[
     {verts = TetrahedronVertsInSphereCircs[tet],
      norm = sphereCirc[[1]]},
     AllTrue[verts, # . norm <= tol &] && 
      AnyTrue[Subsets[verts, {3}], 
       Function[triple, AllTrue[triple, Abs[# . norm] < tol &]]]
     ]
    ]
   ,
   With[
    {centRad = SphereInfoFromCirc[sphereCirc]},
    Function[tet,
     With[
      {verts = TetrahedronVertsInSphereCircs[tet]},
      AllTrue[verts, Norm[# - centRad[[1]]] >= centRad[[2]] - tol &] &&
        AnyTrue[Subsets[verts, {3}], 
        Function[triple, 
         AllTrue[triple, (Abs[Norm[# - centRad[[1]]] - centRad[[2]]] <
              tol) &]]]
      ]
     ]
    ]
   ];

TetrahedronsEqual[tet1_, tet2_] := 
  AllTrue[tet1, SphereCircleIsInList[#, tet2] &];


(* ========================================================== *)
(* GENERATING TETRAHEDRONS *)
(* ========================================================== *)

(* Find Centre Of Mass of vertices of a tetrahedron *)
TetrahedronCOM[tet_] := Mean@TetrahedronVertsInSphereCircs[tet];

(* only reflecting in planes that belong to tetrahedrons that are far f\
rom the centre of mass of vertices is a more efficient way to generate\
 new tetrahedrons *)
ExtremalTetrahedrons[tets_, extremality_] := Module[
   {totalCOM, orderedTets},
   totalCOM = Mean [TetrahedronCOM /@ tets];
   orderedTets = 
    Sort[tets, 
     Norm[TetrahedronCOM[#1] - totalCOM] < 
       Norm[TetrahedronCOM[#2] - totalCOM] &];
   Take[orderedTets, -Ceiling[Length[orderedTets]*(1 - extremality)]]
   ];

(*Given a SphereCirc, get the point closest to the origin *)
PointClosestToOrigin[sphereCirc_] := 
  If[sphereCirc[[2]] == 0, {0, 0, 0},
   Module[
    {cent, rad},
    {cent, rad} = SphereInfoFromCirc[sphereCirc];
    cent - rad * sphereCirc[[1]]
    ]
   ];

(* Planes that are a maximum distance from the mean point closest to o\
rigin *)
ExtremalPlanes[planes_] := Module[
   {totalCOM, orderedPlanes},
   totalCOM = Mean[PointClosestToOrigin /@ planes];
   orderedPlanes = 
    Sort[planes, 
     Norm[PointClosestToOrigin[#1] - totalCOM] < 
       Norm[PointClosestToOrigin[#2] - totalCOM] &];
   Take[orderedPlanes, -Ceiling[Length[planes]*0.2]]
   ];

(* given some (likely just one) tetrahedrons, \
who's planes generate the group, spit out more tetrahedrons *)
MakeTetrahedrons[tets_, k_, n_, extremality_] :=
  If[n == 0, tets,
   Module[
    {allExternalPlanes, nextTets, plane, tet, tuples, i},
    (* Any plane that are shared by two tetrahedrons is an internal pl\
ane *)
    (* we disclude these, 
    because they will not result in new tetrahedra *)
    
    allExternalPlanes = 
     DeleteDuplicates[
      NumericallyConditionSphereCircle /@ 
       Flatten[ExtremalTetrahedrons[tets, extremality]], 
      SphereCirclesAreEqual];
    tuples = NonRepeatingTuples[allExternalPlanes, k];
    Print[Length[tuples]];
    nextTets = 
     Flatten[Table[
       ReflectAcrossMultipleNumeric[#, tuple] & /@ tet, {tuple, 
        tuples}, {tet, tets}], 1];
    Print[Length[nextTets]];
    nextTets = UniqueifyTetrahedrons[nextTets];
    MakeTetrahedrons[nextTets, k, n - 1, extremality]
    ]
   ];

(* The opposite plane will always also be in the group *)
OppositeSphereCirc[SphereCircle[u_, r_]] := SphereCircle[-u, r];

(* Reflect each tetrahedron through origin and take union of these new\
 tetrahedrons with old *)
SymmetrizeTetrahedrons[tets_] := Module[
   {oppositeTets},
   oppositeTets = Map[OppositeSphereCirc, tets, {2}];
   Join[tets, oppositeTets]
   ];

(* ========================================================== *)
(* NUMERIC FAST DISTINGUISHING OF TETRAHEDRONS *)
(* ========================================================== *)

SphereCircsEqualCompiled = Compile[
   {r1, x1, y1, z1, r2, x2, y2, z2, tol},
   If[r1 < tol && r2 < tol,
    (*If both planes are equatorial they are equal if u1 = -u2 *)
    If[(Abs[x1 - x2] <= tol && Abs[y1 - y2] <= tol && 
        Abs[z1 - z2] <= tol) || (Abs[x1 + x2] <= tol && 
        Abs[y1 + y2] <= tol && Abs[z1 + z2] <= tol), 1, 0],
    If[Abs[r1 - r2] <= tol && Abs[x1 - x2] <= tol && 
      Abs[y1 - y2] <= tol && Abs[z1 - z2] <= tol, 1, 0]
    ],
   CompilationTarget -> "C"];

SphereCircleInListCompiled = Compile[{{s, _Real, 1}, {list, _Real, 2}},
   Module[{i, n},
    n = Length[list];
    Catch[
     Do[
      If[
       SphereCircsEqualCompiled[s[[1]], s[[2]], s[[3]], s[[4]], 
         list[[i, 1]], list[[i, 2]], list[[i, 3]], list[[i, 4]], 
         0.01] == 1,
       Throw[1]], {i, n}];
     0
     ]
    ],
   CompilationTarget -> "C"
   ];

TetrahedronsEqualCompiled = Compile[
   {
    {tet1, _Real, 2},
    {tet2, _Real, 2}
    },
   Module[
    {i},
    Catch[
     Do[
      If[SphereCircleInListCompiled[tet1[[i]], tet2] == 0, 
       Throw[False]],
      {i, 4}];
     True
     ]
    ]
   ];

ExtractSphereCircArgs[SphereCircle[u_, r_]] := {r, u[[1]], u[[2]], 
   u[[3]]};

ReformSphereCircFromArgs[{r_, x_, y_, z_}] := 
  SphereCircle[{x, y, z}, r];

(* ~10x speed boost over DeleteDuplicates[...,TetrahedronsEqual]  yay! \
*)
UniqueifyTetrahedrons[tets_] := Module[
   {numericTets},
   numericTets = Map[ExtractSphereCircArgs, tets, {2}];
   numericTets = 
    DeleteDuplicates[numericTets, TetrahedronsEqualCompiled];
    Map[ReformSphereCircFromArgs, numericTets, {2}]
   ];

(* ========================================================== *)
(* PLOTTING *)
(* ========================================================== *)

ParameteriseTriangleFace[{v1_, v2_, v3_}] := 
  Function[{u, v}, v1 + u (v2 - v1) + v (v3 - v1)];

ParameteriseEdge[{v1_, v2_}] := Function[t, v1 + t (v2 - v1)];

(*Function to plot the image of an edge under f*)
PlotImageOfEdge[edge_, f_, colour_ : Black] := 
  ParametricPlot3D[f[ParameteriseEdge[edge][t]], {t, 0, 1}, 
   PlotStyle -> Directive[(*Thickness[0.008]*)Thick, colour]];

(*Given four euclidean planes ({n,c} corr to n.x==c), \
give the four vertices corr to that tetrahedron *)
TetrahedronVertsInEuclideanPlanes[planes_] := Module[
    {verts, x, y, z},
   verts = 
    Table[Solve[{Dot[planes[[i, 1]], {x, y, z}] == planes[[i, 2]], 
       Dot[planes[[j, 1]], {x, y, z}] == planes[[j, 2]], 
       Dot[planes[[k, 1]], {x, y, z}] == planes[[k, 2]]}, {x, y, 
       z}], {i, 1, 4}, {j, i + 1, 4}, {k, j + 1, 4}];
   ReplaceAll[{x, y, z}, #] & /@ Flatten[verts, 3]
   ];

PlotImageOfTriangle[verts_, f_, colour_ : Orange, opacity_: 0.9] :=
  ParametricPlot3D[
   f[ParameteriseTriangleFace[verts][u, v]],
   {u, 0, 1}, {v, 0, 1 - u},
   (* Change opacity to 0.9 *)
   Mesh->None,
   PlotStyle -> Directive[Opacity[opacity], colour]
   (* MeshFunctions -> Function[{u,v}, Norm[ParameteriseTriangleFace[verts][u,v]]], *)
   (* Mesh -> {{0.7}} *)
   ];

PlotImageOfTetrahedronInPlanes[planes_, f_, colouriseEdges_ : False, opacity_: 0.9] :=
   Module[
   {vertices, faces, edges},
   vertices = TetrahedronVertsInEuclideanPlanes[planes];
   faces = Subsets[vertices, {3}];
   edges = Subsets[vertices, {2}];
   If[colouriseEdges,
    Join[
     MapThread[
      PlotImageOfTriangle[#1, f, #2] &, {faces, {Red, Green, Blue, 
        Orange}}],
      MapThread[
      PlotImageOfEdge[#, f, #2] &, {edges, tetrahedronEdgeColours}]
     ],
    Join[
     MapThread[
      PlotImageOfTriangle[#1, f, #2, opacity] &, {faces, 
       tetrahedronFaceColours}],
      PlotImageOfEdge[#, f] & /@ edges]
    ]
   ];

PlotTetrahedronInSphereCircles[sphereCircles_,
   colouriseEdges_ : False, opacity_: 0.9, capped_: False] := With[
   (* Transform of SphereCircle to corr. 
   plane in Klein model is very simple! *)
   {planes = {#[[1]], #[[2]]} & /@ sphereCircles},
   PlotImageOfTetrahedronInPlanes[planes, If[capped, KleinToDiskCapped, KleinToDisk], colouriseEdges, opacity]
   ];

PlotImageOfTetrahedronInSphereCircles[sphereCircles_, f_, 
   colouriseEdges_ : False] := With[
   (* Transform of SphereCircle to corr. 
   plane in Klein model is very simple! *)
   {planes = {#[[1]], #[[2]]} & /@ sphereCircles},
   PlotImageOfTetrahedronInPlanes[planes, f@*KleinToDisk, 
    colouriseEdges]
   ];

PlotKleinImageOfTetrahedronInSphereCircles[sphereCircles_, f_, 
   colouriseEdges_ : False, opacity_: 0.9] := With[
   (* Transform of SphereCircle to corr. 
   plane in Klein model is very simple! *)
   {planes = {#[[1]], #[[2]]} & /@ sphereCircles},
   PlotImageOfTetrahedronInPlanes[planes, f, colouriseEdges, opacity]
   ];

(* ---------------------------------------------------------- *)
(* INFO PLOTS *)
(* ---------------------------------------------------------- *)

TriangleInfoPlot[faceColor_, angles_, edgeColours_, 
   pts_ : {{0, 0}, {0.3, 1}, {1.3, 0.7}}] := Module[
   {edges, anglesDegreesNumeric},
   edges = Table[{pts[[i]], pts[[Mod[i, 3] + 1]]}, {i, 1, 3}];
   anglesDegreesNumeric = 180./Pi * angles;
   Graphics[{
     {faceColor, Polygon[pts]},
     {edgeColours[[1]], Thickness[0.05], 
      Line[edges[[1]]]}, {edgeColours[[2]], Thickness[0.05], 
      Line[edges[[2]]]}, {edgeColours[[3]], Thickness[0.05], 
      Line[edges[[3]]]},
     {Text[Style[anglesDegreesNumeric[[1]], Small], 
       TextPositionAtXFromTriple[pts]],
      Text[Style[anglesDegreesNumeric[[2]], Small], 
       TextPositionAtXFromTriple[pts[[{2, 1, 3}]]]],
      Text[Style[anglesDegreesNumeric[[3]], Small], 
       TextPositionAtXFromTriple[pts[[{3, 1, 2}]]]]},
     Text[N[Pi - Total[angles]], {0.3, -0.6}]
     }]];

EdgeInfoPlot[edgeColour_, eq_, dihedral_, length_] :=
  Graphics[{
    {edgeColour, Thickness[0.6], Line[{{0, 0}, {0, 1}}]},
    Text[Style[eq, Large], {0.3, 0.9}],
    Text[Style[dihedral, Small], {0.3, 0.5}],
    Text[Style[length, Small], {0.3, 0.2}]
    },
   ImageSize -> Small];

TextPositionAtXFromTriple[{x_, y_, z_}] :=
  x + 0.3*(x - Mean[{x, y, z}]);

TetrahedronInfo[planes_] := Module[
   {vertPoints, edgeLengths, dihedralAngles, reorderDihedrals, 
    edgeEqns, edgePlots, vertsByFaces, faceAngles, 
    anglesEdgesFromPlanes, trianglePlots, reorderEdgeColours},
   vertPoints = TetrahedronVertsInSphereCircs[planes];
   edgeLengths = 
    N[DistanceInDisk[#[[1]], #[[2]]] & /@ Subsets[vertPoints, {2}]];
   dihedralAngles = 
    FullSimplify[
     IntersectionAngle[#[[1]], #[[2]]] & /@ Subsets[planes, {2}]];
   reorderEdgeColours = {1, 2, 4, 3, 5, 6};
   edgeEqns = {#[[1]] + #[[2]], #[[1]] + #[[3]], #[[1]] + #[[4]], #[[
         2]] + #[[3]], #[[2]] + #[[4]], #[[3]] + #[[4]]} &@
     tetrahedronFaceColours;
   edgePlots = 
    MapThread[
     EdgeInfoPlot, {tetrahedronEdgeColours[[reorderEdgeColours]], 
      edgeEqns, dihedralAngles, edgeLengths[[reorderEdgeColours]]}];
   edgePlots = Grid[Partition[edgePlots, UpTo[3]], Frame -> All];
   
   anglesEdgesFromPlanes[planeNum_] := {
      {{3, 2, 1}, {1, 4, 2}},
      {{3, 1, 2}, {3, 5, 1}},
      {{3, 2, 1}, {2, 6, 3}},
      {{3, 1, 2}, {5, 6, 4}}
      }[[planeNum]];
   
   vertsByFaces = 
    Table[Table[
      Join[{a}, others], {others, 
       Subsets[Complement[planes, {a}], {2}]}], {a, planes}];
   faceAngles = Map[FaceAngleFromTripleOfPlanes, vertsByFaces, {2}];
   (*faceAngles = N[180./Pi *faceAngles];*)
   trianglePlots = Table[TriangleInfoPlot[
      tetrahedronFaceColours[[planeNum]],
      faceAngles[[planeNum]][[anglesEdgesFromPlanes[planeNum][[1]]]],
      tetrahedronEdgeColours[[anglesEdgesFromPlanes[planeNum][[2]]]]
      ],
     {planeNum, Range[4]}];
   
   trianglePlots = 
    Grid[Partition[trianglePlots, UpTo[4]], Frame -> All];
   Grid[{{edgePlots, trianglePlots}}]
   ];
