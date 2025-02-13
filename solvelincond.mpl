interface(errorbreak=3):
kernelopts(assertlevel=1):

SolveLinearCondition := proc(f, beta, params)
    local m, vars, X, i, j, cond,
        monos, substitutions, mono, c, v, substituted;
    m := nops(beta);
    monomials = [];
    X := Matrix(m);
    vars := {};
    for i from 1 to m do
        for j from 1 to m do
            v := ifelse(i <= j, cat('x', i, j), cat('x', j, i));
            X[i, j] := v;
            vars := vars union {v};
        end do;
    end do;
    cond := (Matrix(beta) . X . Matrix(beta)^%T)[1, 1] - f;
    monos := convert(Matrix(beta)^%T . Matrix(beta), set);
    substitutions := [];
    for mono in monos do
        c := cond;
        for v in indets(beta, name) do
            c := coeff(c, v, degree(mono, v));
        end do;
        c := subs(substitutions, c);
        substituted := false;
        for v in vars do
            if v in indets(c) then
                substitutions := [
                    op(substitutions),
                    v = expand(-c / coeff(c, v) + v)
                ];
                vars := vars minus {v};
                substituted := true;
                break;
            end if;
        end do;
        ASSERT(substituted);
    end do;
    vars := convert(vars, list);
    X := subs(substitutions, X);
    WARNING("cond:", expand(subs(substitutions, cond)));
    # check if the equation is completely eliminated
    ASSERT(expand(subs(substitutions, cond)) = 0);
    ASSERT(expand((Matrix(beta) . X . Matrix(beta)^%T)[1, 1] - f) = 0);
    X, vars
end proc:
