read("src/random.mpl"):

Conjunction := proc(F)
    local i, f;
    f := true;
    for i from 1 to nops(F) do
        if F[i] = false then
            return false;
        elif F[i] = true then
            next;
        elif f = true then
            f := F[i];
        else
            f := And(f, F[i]);
        end if;
    end do;
    f
end proc:

Disjunction := proc(F)
    local i, f;
    f := false;
    for i from 1 to nops(F) do
        if F[i] = true then
            return true;
        elif F[i] = false then
            next;
        elif f = false then
            f := F[i];
        elif f = F[i] then
            next;
        else
            f := Or(f, F[i]);
        end if;
    end do;
    f
end proc:

EvalNonZero := proc(f)
    if type(f, rational) then
        return evalb(f <> 0);
    end if;
    return IsNonZero(f);
end proc:

SignPattern := proc(f, eta)
    local h, s;
    h := simplify(f);
    if type(h, rational) then
        return true;
    end if;
    s := eval(h, eta);
    ASSERT(s <> 0);
    return ifelse(s > 0, IsPositive(h), IsNegative(h));
end proc:

EvalTree := proc(v, S)
    if type(v, boolean) then
        return v;
    elif op(0, v) = `And` then
        return Conjunction([EvalTree(op(1, v), S), EvalTree(op(2, v), S)]);
    elif op(0, v) = `Or` then
        return Disjunction([EvalTree(op(1, v), S), EvalTree(op(2, v), S)]);
    elif op(0, v) = `IsNonZero` then
        return evalb(subs(S, op(1, v)) <> 0);
    elif op(0, v) = `IsPositive` then
        return evalb(subs(S, op(1, v)) > 0);
    elif op(0, v) = `IsNegative` then
        return evalb(subs(S, op(1, v)) < 0);
    elif op(0, v) = `IsSignature` then
        return evalb(Signature(subs(S, op(1, v))) = op(2, v));
    else
        WARNING("Unknown operator:", op(0, v), "in", v);
        ASSERT(false);
    end if;
end proc:

TestEvalTree := proc()
    local v;
    v := And(Or(IsPositive(a), IsNegative(a)), IsNonZero(a));
    ASSERT(EvalTree(v, [a = 0]) = false);
end proc:

TestEvalTree();


NaiveMonomialBasis := proc(F, vars, params)
    local tord, G, B, rv;
    tord := tdeg(op(vars));
    G := Groebner:-Basis(F, prod(tord, tdeg(op(params))));
    B, rv := Groebner:-NormalSet(G, tord);
    B, rv, G, tord
end proc:

HermiteMatrix := proc(g, B, rv, G, tord)
    local M, M_g, i, j, M_i_j;
    # WARNING("Start computing Hermite matrix of", g);
    M := Matrix(nops(B), nops(B));
    if g = 1 then
        M_g := [];
        for i from 1 to nops(B) do
            # WARNING("Computing multiplication matrix of", B[i]);
            M_g := [op(M_g), Groebner:-MultiplicationMatrix(B[i], B, rv, G, tord)];
        end do;
        for i from 1 to nops(B) do
            for j from i to nops(B) do
                M[i, j] := LinearAlgebra:-Trace(M_g[i] . M_g[j]);
            end do;
        end do;
        for i from 1 to nops(B) do
            for j from 1 to i - 1 do
                M[i, j] := M[j, i];
            end do;
        end do;
        # WARNING("End computing Hermite matrix");
        return M;
    end if;
    for i from 1 to nops(B) do
        for j from i to nops(B) do
            M_i_j := Groebner:-MultiplicationMatrix(g * B[i] * B[j], B, rv, G, tord);
            M[i, j] := LinearAlgebra:-Trace(M_i_j);
        end do;
    end do;
    for i from 1 to nops(B) do
        for j from 1 to i - 1 do
            M[i, j] := M[j, i];
        end do;
    end do;
    # WARNING("End computing Hermite matrix");
    M
end proc:

ASSERT(HermiteMatrix(1, NaiveMonomialBasis([x^2+b*x+c], [x], [b, c]))[2, 2] = b^2-2*c);

LeadPrincMinors := proc(M)
    local L, i, minor;
    ASSERT(LinearAlgebra:-RowDimension(M) = LinearAlgebra:-ColumnDimension(M));
    L := [];
    for i from 1 to LinearAlgebra:-RowDimension(M) do
        minor := LinearAlgebra:-Determinant(LinearAlgebra:-SubMatrix(M, 1..i, 1..i));
        L := [op(L), numer(minor) * denom(minor)];
    end do;
    L
end proc:

CartesianProduct := proc(a, b)
    local L, x, y;
    L := [];
    for x in a do
        for y in b do
            L := [op(L), [op(x), op(y)]];
        end do;
    end do;
    L
end proc:

CartesianPower := proc(a, n)
    foldl(CartesianProduct, [[]], [[]], seq(a, 1 .. n))
end proc:

ASSERT(CartesianPower([[1], [2]], 0) = [[]]);
ASSERT(CartesianPower([[1], [2]], 1) = [[1], [2]]);
ASSERT(CartesianPower([[1], [2]], 2) = [[1, 1], [1, 2], [2, 1], [2, 2]]);

KroneckerPower := proc(M, n)
    foldl(LinearAlgebra:-KroneckerProduct, Matrix(1, 1, [1]), Matrix(1, 1, [1]), seq(M, 1 .. n))
end proc:

PowerProduct := proc(q, alpha)
    local s, i;
    ASSERT(nops(q) = nops(alpha));
    s := 1;
    for i from 1 to nops(q) do
        s := s * q[i]^alpha[i];
    end do;
    s
end proc:

Var := proc(L)
    local n, s, i;
    n := 0;
    ASSERT(L[1] = 1);
    s := sign(L[1]);
    for i from 2 to nops(L) do
        if L[i] <> 0 and s * sign(L[i]) = -1 then
            s := sign(L[i]);
            n := n + 1;
        end if;
    end do;
    n
end proc:

ASSERT(Var([1, -1, 1, 1]) = 2);

InverseCoefficients := proc(L)
    map(i -> (-1)^(i-1) * L[i], [seq(1..nops(L))])
end proc:

CharacteristicPolynomialCoefficients := proc(A)
    local p;
    ASSERT(LinearAlgebra:-Equal(LinearAlgebra:-Transpose(A), A));
    p := LinearAlgebra:-CharacteristicPolynomial(A, t);
    ListTools:-Reverse(PolynomialTools:-CoefficientList(p, t))
end proc:

Signature := proc(A)
    local L_plus;
    L_plus := CharacteristicPolynomialCoefficients(A);
    ASSERT(L_plus[1] = 1);
    Var(L_plus) - Var(InverseCoefficients(L_plus))
end proc:

ASSERT(Signature(Matrix([[1]])) = 1);
ASSERT(Signature(Matrix([[1, 2], [2, 3]])) = 0);
ASSERT(Signature(Matrix([[2, 0], [0, 0]])) = 1);


Mat := proc(ada, sigma)
    local M, i, j, k;
    ASSERT(type(ada, list) and type(sigma, list));
    M := Matrix(nops(ada), nops(sigma));
    for i from 1 to nops(ada) do
        for j from 1 to nops(sigma) do
            M[i, j] := PowerProduct(sigma[j], ada[i]);
        end do;
    end do;
    M
end proc:

ASSERT(LinearAlgebra:-Equal(
    Mat([[0], [1], [2]], [[0], [1], [-1]]),
    Matrix([[1, 1, 1], [0, 1, -1], [0, 1, 1]]))
);

RankProfile := proc(M)
    local L, R, r, i, rc;
    R := LinearAlgebra:-Rank(M);
    L := [];
    r := 0;
    for i from 1 to LinearAlgebra:-RowDimension(M) do
        rc := LinearAlgebra:-Rank(M[[op(L), i], ..]);
        if rc = r + 1 then
            L := [op(L), i];
            r := rc;
        end if;
    end do;
    ASSERT(r = R);
    L
end proc:

TestRankProfile := proc()
    local M;
    M := Matrix([[1, 2, 3], [4, 5, 6], [7, 8, 9]]);
    ASSERT(RankProfile(M) = [1, 2]);
end proc:

TestRankProfile();


Classification := NoSamplePointsClassification;


NoSamplePointsClassification := proc(g, params, filter, B, rv, G, tord)
    local s, w_f, U, ada, sigma, M, H_g_alphas, rk_alphas, h_alphas, minors,
          alpha, H_g_alpha, rk_alpha, h_alpha, M_inverse, c_1, i, w, iterator,
          t, w_t, H_1, M_g, g_i, M_g_i,
          cond_w, cond_w_f, cond_minors, minor;
    s := nops(g);
    w_f := map(p -> Groebner:-LeadingCoefficient(p, tord), G);
    U := LinearAlgebra:-RandomMatrix(nops(B));
    ada := CartesianPower([[0], [1], [2]], s);
    sigma := CartesianPower([[0], [1], [-1]], s);
    M := Matrix([[1, 1, 1], [0, 1, -1], [0, 1, 1]]);
    M := KroneckerPower(M, s);
    H_g_alphas := [];
    minors := {};
    WARNING("Computing Hermite matrix of 1");
    H_1 := HermiteMatrix(1, B, rv, G, tord);
    M_g := [];
    for g_i in g do
        WARNING("Computing multiplication matrix of", g_i);
        M_g_i := Groebner:-MultiplicationMatrix(g_i, B, rv, G, tord);
        M_g := [op(M_g), M_g_i];
    end do;
    for alpha in ada do
        WARNING("Computing Hermite matrix of H_g_", alpha);
        H_g_alpha := H_1;
        for i from 1 to s do
            H_g_alpha := H_g_alpha . LinearAlgebra:-MatrixPower(M_g[i], alpha[i]);
        end do;
        H_g_alphas := [op(H_g_alphas), H_g_alpha];
    end do;
    M_inverse := LinearAlgebra:-MatrixInverse(M);
    c_1 := Vector[row](LinearAlgebra:-ColumnDimension(M), 0);
    for i from 1 to nops(sigma) do
        if filter(sigma[i]) then
            c_1 := c_1 + M_inverse[i];
        end if;
    end do;
    w := IsLinearCombSignature(H_g_alphas, c_1);
    cond_w := EvalNot(w);
    cond_w_f := EvalNonZero(w_f);
    cond_minors := true;
    for minor in minors do
        cond_minors := Conjunction([cond_minors, EvalNonZero(minor)]);
    end do;
    sigma, [[Conjunction([cond_w, cond_w_f, cond_minors]), [], 1]]
end proc:


PositiveCondition := proc(results)
    local condition, result;
    condition := false;
    for result in results do
        if result[3] > 0 then
            condition := Disjunction([condition, result[1]]);
        end if;
    end do;
    condition
end proc:
