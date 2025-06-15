interface(errorbreak=3):
kernelopts(assertlevel=1):

read("src/classification.mpl"):
read("src/msolve_path.mpl"):
read("src/msolve.mpl"):
read("src/random.mpl"):

TypeTools:-AddType('LinearMatrix', 'record(mat::`Matrix`(polynom), params::list(symbol), vars::list(symbol))');

LinearMatrix := proc(mat::`Matrix`(polynom), params::list(symbol), vars::list(symbol))::`LinearMatrix`;
    Record(
        "mat"::'Matrix'(polynom) = mat,
        "params"::list(symbol) = params,
        "vars"::list(symbol) = vars
    )
end proc:

TypeTools:-AddType('Ideal', 'record(gens::list(polynom), params::list(symbol), vars::list(symbol), auxvars::list(list(symbol)))');

Ideal := proc(gens::list(polynom), params::list(symbol), vars::list(symbol), auxvars::list(list(symbol)):=[])::`Ideal`;
    Record(
        "gens"::list(polynom) = gens,
        "params"::list(symbol) = params,
        "vars"::list(symbol) = vars,
        "auxvars"::list(list(symbol)) = auxvars
    )
end proc:


Jacobian := proc(F::`Ideal`)::`Matrix`(polynom);
    local vars;
    vars := [op(F["vars"]), op(ListTools:-Flatten(F["auxvars"]))];
    Matrix(map(f -> convert(VectorCalculus:-Gradient(f, vars), list), F["gens"]))
end proc:

TestJacobian := proc()
    local F;
    F := Ideal([x^2 + y^2 - 1], [], [x, y]);
    ASSERT(LinearAlgebra:-Equal(Jacobian(F), Matrix([[2*x, 2*y]])));
end proc:

TestJacobian();


Image := proc(V::`Ideal`, M::`Matrix`(rational))::`Ideal`;
    local F;
    F := eval(V["gens"], zip((k, v) -> k = v, V["vars"], convert(Matrix(V["vars"]) . M^%T, list)));
    Ideal(F, V["params"], V["vars"], V["auxvars"])
end proc:

TestImage := proc()
    local V, M, V2;
    V := Ideal([x_1^2 - x_2^2 - x_3^2 - 1], [], [x_1, x_2, x_3]);
    M := RandomInvertibleMatrix(nops(V["vars"]));
    V2 := Image(Image(V, M), LinearAlgebra:-MatrixInverse(M));
    ASSERT(nops(V["gens"]) = nops(V2["gens"]));
end proc:

TestImage();


PSDMatrixCond := proc(A::`LinearMatrix`, M::`Matrix`(rational))::list(polynom);
    local m, g;
    m := LinearAlgebra:-RowDimension(A["mat"]);
    g := PolynomialTools:-CoefficientList(expand(LinearAlgebra:-Determinant(A["mat"] + t * LinearAlgebra:-IdentityMatrix(m))), t);
    Image(Ideal(g[1..-2], A["params"], A["vars"]), M)["gens"]
end proc:

TestPSDMatrixCond := proc()
    local A, q;
    A := LinearMatrix(Matrix([[1, 2], [2, 4]], [], []));
    q := PositiveSemidefiniteMatrixCond(A);
    ASSERT(q = [5]);
end proc:


DeterminantalVariety := proc(A::`LinearMatrix`, r::integer)::`Ideal`;
    local m;
    m := LinearAlgebra:-ColumnDimension(A["mat"]);
    ASSERT(0 <= r and r <= m - 1);
    Ideal(Minors(A["mat"], r + 1), A["params"], A["vars"])
end proc:

IncidenceVarietyFallback := proc(A::`LinearMatrix`, r::integer, U::`Matrix`(rational), S::`Matrix`(rational), var::symbol:=u)::`Ideal`;
    local m, Y, i, j, gens;
    m := LinearAlgebra:-ColumnDimension(A["mat"]);
    ASSERT(0 <= r and r <= m - 1);
    Y := Matrix([seq([seq(cat(var, _, i, _, j), j = 1 .. m - r)], i = 1 .. m)]);
    gens := [op(convert((A["mat"] . Y)^%T, list)), op(convert((U.Y - S)^%T, list))];
    Ideal(gens, A["params"], A["vars"], [convert(Y^%T, list)])
end proc:

IncidenceVariety := proc(A::`LinearMatrix`, r::integer, iota::list(integer), var::symbol:=u, succinct::integer:=2)::`Ideal`;
    local m, Y, U, G, gens, i, j, auxvars;
    m := LinearAlgebra:-ColumnDimension(A["mat"]);
    ASSERT(0 <= r and r <= m - 1);
    ASSERT(nops(iota) = m - r);
    Y := Matrix([seq([seq(cat(var, _, i, _, j), j = 1 .. m - r)], i = 1 .. m)]);
    U := LinearAlgebra:-IdentityMatrix(m - r);
    if succinct = 0 then
        gens := [op(convert((A["mat"] . Y)^%T, list)), op(convert((Y[iota, 1 .. m - r] - U)^%T, list))];
        return Ideal(gens, A["params"], A["vars"], [convert(Y^%T, list)]);
    end if;
    # https://homepages.laas.fr/henrion/papers/exactlmi.pdf, page 10 (eliminating redundancies)
    G := LinearAlgebra:-Map(f -> eval(f, convert(LinearAlgebra:-Zip((k, v) -> k = v, Y[iota, 1 .. m - r], U), list)), A["mat"] . Y);
    gens := [];
    for i from 1 to m do
        for j from 1 to m - r do
            if i >= j then
                gens := [op(gens), G[i, j]];
            end if;
        end do;
    end do;
    if succinct = 1 then
        gens := [op(gens), op(convert((Y[iota, 1 .. m - r] - U)^%T, list))];
        return Ideal(gens, A["params"], A["vars"], [convert(Y^%T, list)]);
    end if;
    # Furthermore, we can drop m(m-r) auxiliary variables and (m-r)^2 equations
    auxvars := [];
    for i from 1 to m do
        if not i in iota then
            auxvars := [op(auxvars), op(convert(Y[i, 1 .. m - r], list))];
        end if;
    end do;
    Ideal(gens, A["params"], A["vars"], [auxvars])
end proc:


Minors := proc(A::`Matrix`, k::integer)::list;
    local rs, cs;
    rs := combinat:-choose(LinearAlgebra:-RowDimension(A), k);
    cs := combinat:-choose(LinearAlgebra:-ColumnDimension(A), k);
    ListTools:-Flatten(map(r -> map(c -> LinearAlgebra:-Determinant(A[r, c]), cs), rs))
end proc:

LagrangeSystem := proc(V::`Ideal`, var::symbol:=l,
    fallback::boolean:=false, saturate::boolean:=false)::`Ideal`;
    local J, z, alpha, gens, k, V2, v2_det;
    J := Jacobian(V);
    if fallback then
        gens := [op(Minors(J[1..-1, 2..-1], LinearAlgebra:-RowDimension(J))), op(V["gens"])];
        V2 := Ideal(gens, V["params"], V["vars"], V["auxvars"]);
    else
        z := Matrix([[seq(cat(var, _, k), k = 1 .. nops(V["gens"]))]]);
        alpha := Matrix([[seq(ifelse(k = 1, 1, 0), k = 1 .. LinearAlgebra:-ColumnDimension(J))]]);
        gens := [op(V["gens"]), op(convert(z . J - alpha, list))];
        V2 := Ideal(gens, V["params"], V["vars"], [op(V["auxvars"]), convert(z, list)]);
    end if;
    if saturate then
        v2_det := LinearAlgebra:-Determinant(Jacobian(V2));
        V2 := Ideal([op(V2["gens"]), cat(var, _, 0) * v2_det - 1], V2["params"], V2["vars"], [op(V2["auxvars"]), [cat(var, _, 0)]]);
    end if;
    V2
end proc:

TestLagrangeSystem := proc()
    local V, L;
    V := Ideal([x_1^2 - x_2^2 - x_3^2 - 1], [], [x_1, x_2, x_3]);
    L := LagrangeSystem(V);
    ASSERT(nops(L["gens"]) >= 3);
end proc:

TestLagrangeSystem();


Lift := proc(V::`Ideal`, var::symbol, t::rational)::`Ideal`;
    Ideal([var - t, op(V["gens"])], V["params"], [var, op(V["vars"])], V["auxvars"])
end proc:

TestLift := proc()
    local V, V2, L;
    V := Ideal([x_1^2 - x_2^2 - x_3^2 - 1], [], [x_1, x_2, x_3]);
    V2 := Lift(V, x_0, 42);
    ASSERT(nops(V2["gens"]) = nops(V["gens"]) + 1);
end proc:

TestLift();


Fiber := proc(V::`Ideal`, t::rational)::`Ideal`;
    Ideal(subs(V["vars"][1] = t, V["gens"]), V["params"], V["vars"][2..-1], V["auxvars"])
end proc:

TestFiber := proc()
    local V;
    V := Ideal([x_1^2 - x_2^2 - x_3^2 - 1], [], [x_1, x_2, x_3]);
    ASSERT(Fiber(V, 42)["gens"] = [42^2 - x_2^2 - x_3^2 - 1]);
end proc:

TestFiber();


Solve := proc(V::`Ideal`)::list(list(`=`));
    local q;
    q := SolveTools:-PolynomialSystem(V["gens"], [op(V["vars"]), op(ListTools:-Flatten(V["auxvars"]))], engine=groebner);
    map(s -> map(var -> var = eval(var, s), V["vars"]), [q]);
end proc;


ExpectedDimension := proc(n::integer, m::integer, r::integer)::integer;
    n - (m - r + 1) * (m - r) / 2
end proc:

PolarVarietiesRec := proc(V::`Ideal`, d::integer, M::`Matrix`(rational), T::list(rational))::list(`Ideal`);
    local m, w_1, w_2;
    if d < 0 then
        return [];
    end if;
    w_1 := [LagrangeSystem(Image(V, M))]:
    w_2 := PolarVarietiesRec(Fiber(V, T[1]), d - 1, M[2 .. nops(V["vars"]), 2 .. nops(V["vars"])], T[2 .. nops(T)]);
    [op(w_1), op(map(v -> Lift(v, V["vars"][1], T[1]), w_2))]
end proc:

TestPolarVarietiesRec := proc()
    local V, n, M;
    V := Ideal([x_1^2 - x_2^2 - x_3^2 - 1], [], [x_1, x_2, x_3]);
    n := nops(V["vars"]);
    M := LinearAlgebra:-IdentityMatrix(n);
    ASSERT(nops(PolarVarietiesRec(V, 2, M, [seq(0, n)])) = 3);
end proc:

TestPolarVarietiesRec();


RealDet := proc(A::`LinearMatrix`, M::`Matrix`(rational), T::list(rational),
    fallback::integer:=1)::list(`Ideal`);
    local m, q, r, d, iota, U, S, f;
    m := LinearAlgebra:-ColumnDimension(A["mat"]);
    q := [seq([], m)];
    for r from 0 to m - 1 do
        d := ExpectedDimension(nops(A["vars"]), m, r);
        if d < 0 then
            next;
        end if;
        if fallback = 1 then
            # FIXME: make U and S global
            U := RandomFullRankMatrix(m - r, m);
            S := RandomInvertibleMatrix(m - r);
            f := IncidenceVarietyFallback(A, r, U, S);
            q[r + 1] := [op(q[r + 1]), op(PolarVarietiesRec(f, d, M, T))];
        elif fallback = 2 then
            f := DeterminantalVariety(A, r);
            q[r + 1] := [op(q[r + 1]), op(PolarVarietiesRec(f, d, M, T))];
        else
            for iota in combinat:-choose(m, m - r) do
                f := IncidenceVariety(A, r, iota);
                q[r + 1] := [op(q[r + 1]), op(PolarVarietiesRec(f, d, M, T))];
            end do;
        end if;
    end do;
    q
end proc:

TestRealDet := proc()
    local A, M, T, Q;
    A := LinearMatrix(Matrix([[1, x_1, x_2], [x_1, 1, x_3], [x_2, x_3, 1]]), [], [x_1, x_2, x_3]);
    M := RandomInvertibleMatrix(nops(A["vars"]));
    T := RandomPoint(nops(A["vars"]));
    Q := RealDet(A, M, T, 0);
    ASSERT(nops(ListTools:-Flatten(Q)) = 12);
    Q := RealDet(A, M, T, 1);
    ASSERT(nops(ListTools:-Flatten(Q)) = 4);
end proc:

TestRealDet();


MonomialBasis := proc(V::`Ideal`, cached::boolean:=false, fallback::boolean:=true)
    local gb_hash, gb_cache, G, tord, B, rv, M, i, j, M_i_j, fd;
    if cached then
        gb_hash := StringTools:-Hash(convert(V, string));
        gb_cache := cat("src/data/groebner/", gb_hash, ".mpl");
        if FileTools:-Exists(gb_cache) then
            WARNING("Loading Groebner basis from cache");
            G := op(2, parse(readline(gb_cache)));
            tord := op(2, parse(readline(gb_cache)));
            B, rv := Groebner:-NormalSet(G, tord);
            return B, rv, G, tord;
        end if;
    end if;
    WARNING("Start computing Groebner basis");
    if fallback then
        # Eliminate auxiliary variables
        G := V["gens"];
        G := MSolveGroebner(G, 0, [op(ListTools:-Flatten(V["auxvars"])), op(V["vars"]), op(V["params"])], {"mspath"=mspath, "elim"=nops(ListTools:-Flatten(V["auxvars"]))});
        # or, if we eliminate the Lagrange multipliers first,
        # if nops(V["auxvars"]) >= 2 then
        #     G := MSolveGroebner(G, 0, [op(V["auxvars"][2]), op(V["auxvars"][1]), op(V["vars"]), op(V["params"])], {"mspath"=mspath, "elim"=nops(V["auxvars"][2]), "verb"=2});
        #     G := MSolveGroebner(G, 0, [op(V["auxvars"][1]), op(V["vars"]), op(V["params"])], {"mspath"=mspath, "elim"=nops(V["auxvars"][1]), "verb"=2});
        # end if;
        # or, without msolve,
        # G := Groebner:-Basis(G, lexdeg(ListTools:-Flatten(V["auxvars"]), [op(V["vars"]), op(V["params"])]), method=fgb);
        # G := select(g -> nops(indets(g) intersect convert(ListTools:-Flatten(V["auxvars"]), set)) = 0, G);
        # Now, only gens contains parameters and variables
        if nops(V["params"]) <> 0 then
            G := Groebner:-Basis(G, lexdeg(V["vars"], V["params"]), method=fgb);
        end if;
        tord := tdeg(op(V["vars"]));
    else
        # Don't eliminate auxiliary variables (might be slower)
        if nops(V["params"]) = 0 then
            G := Groebner:-Basis(V["gens"], lexdeg(ListTools:-Flatten(V["auxvars"]), V["vars"]));
        else
            G := Groebner:-Basis(V["gens"], lexdeg(ListTools:-Flatten(V["auxvars"]), V["vars"], V["params"]));
        end if;
        tord := lexdeg(ListTools:-Flatten(V["auxvars"]), V["vars"]);
    end if;
    WARNING("End computing Groebner basis");
    if cached then
        fd := fopen(gb_cache, WRITE);
        fprintf(fd, "G := %a:\n", G);
        fprintf(fd, "tord := %a:\n", tord);
        fclose(fd);
    end if;
    B, rv := Groebner:-NormalSet(G, tord);
    B, rv, G, tord
end proc:

TestMonomialBasis := proc()
    local V, B, rv, G, tord;
    V := Ideal([x^2 + b * x + c], [b, c], [x]);
    B, rv, G, tord := MonomialBasis(V);
    ASSERT(B = [1, x]);
    ASSERT(LinearAlgebra:-Determinant(HermiteMatrix(1, B, rv, G, tord)) = b^2 - 4 * c);
end proc:

TestMonomialBasis();


ParametricSolveLMI := proc(A::`LinearMatrix`, compared::boolean:=true)
    local M, T, Q, g, T_0, A_0, I_m, w, m, r, q, B, rv, G, tord,
        g_non_zero, k, i, M_g_i, filter, s, rs,
        M2, T2, Q2, H2_1;
    M := RandomInvertibleMatrix(nops(A["vars"]));
    T := RandomPoint(nops(A["vars"]));
    Q := RealDet(A, M, T);
    if compared then
        M2 := RandomInvertibleMatrix(nops(A["vars"]));
        T2 := RandomPoint(nops(A["vars"]));
        Q2 := RealDet(A, M2, T2);
    end if;
    g := PSDMatrixCond(A, M);
    # we use 42 instead of 0, so that at least Motzkin is non-trivial
    T_0 := [seq(42, nops(A["vars"]))];
    # of course, we can also use a random point
    # T_0 := RandomTools:-Generate(list(integer, nops(A["vars"])));
    A_0 := LinearMatrix(subs(zip((k, v) -> k = v, A["vars"], T_0), A["mat"]), A["params"], A["vars"]);
    I_m := LinearAlgebra:-IdentityMatrix(nops(A["vars"]));
    w := Conjunction(map(f -> ifelse(type(f, rational), evalb(f > 0), IsPositive(f)), PSDMatrixCond(A_0, I_m)));
    WARNING("Number of zero-dimensional systems:", nops(ListTools:-Flatten(Q)));
    m := LinearAlgebra:-ColumnDimension(A["mat"]);
    for r from m - 1 to 0 by -1 do
        for k from 1 to nops(Q[r + 1]) do
            q := Q[r + 1][k];
            B, rv, G, tord := MonomialBasis(q);
            g_non_zero := [];
            for i from 1 to m do
                M_g_i := Groebner:-MultiplicationMatrix(g[i], B, rv, G, tord);
                if not LinearAlgebra:-Equal(M_g_i, LinearAlgebra:-ZeroMatrix(nops(B))) then
                    g_non_zero := [op(g_non_zero), g[i]];
                end if;
            end do;
            ASSERT(nops(g_non_zero) <= r + 1);
            filter := s -> andmap(c -> c >= 0, s);
            if compared then
                H2_1 := HermiteMatrix(1, MonomialBasis(Q2[r + 1][k]));
                s, rs := Classification(g_non_zero, A["params"], filter, B, rv, G, tord, true, H2_1);
            else
                s, rs := Classification(g_non_zero, A["params"], filter, B, rv, G, tord);
            end if;
            w := Disjunction([w, PositiveCondition(rs)]);
        end do;
    end do;
    w
end proc:
