#!/usr/bin/env wolframscript

TimeQE2[fname_] :=
    Module[{lines, data, vars, matrix, g, cond, time},
        lines = Import[fname, "Lines"];
        data = ToExpression[StringSplit[lines, ","]];
        vars = data[[1]];
        matrix = data[[2 ;; ]];
        g = CoefficientList[Det[matrix + lambda * IdentityMatrix[Length[
            matrix]]], lambda];
        cond = Thread[g >= 0];
        time = Timing[Resolve[Exists[Evaluate[vars], cond], Reals]][[
            1]];
        time
    ];

(*
Example usage:
Print[TimeQE2["examples/data/mkn11.dat"]]
*)
