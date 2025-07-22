#!/usr/bin/env wolframscript

SetDirectory["submissions/generic-param-lmi-poster/images"]

A[x_, y_, z_] := {{1, x, y}, {x, 1, z}, {y, z, 1}}
Export[
    "spectrahedron.png",
    RegionPlot3D[
        PositiveSemidefiniteMatrixQ[A[x, y, z]],
        {x, -(21/20), 21/20}, {y, -(21/20), 21/20}, {z, -(21/20), 21/20},
        PlotStyle -> Directive[GrayLevel[1], Opacity[0.9]],
        Mesh -> All,
        MeshFunctions -> Automatic,
        PlotPoints -> 20,
        Lighting -> {"Ambient", White},
        ViewPoint -> {1, 3/5, 4/5}
    ],
    ImageResolution -> 300
]
