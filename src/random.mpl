interface(errorbreak=3):
kernelopts(assertlevel=1):

RandomFullRankMatrix := proc(m::integer, n::integer)::`Matrix`(rational);
    local A;
    while true do
        A := LinearAlgebra:-RandomMatrix(m, n);
        if LinearAlgebra:-Rank(A) = min(m, n) then
            break;
        end if;
    end do;
    A
end proc:

RandomInvertibleMatrix := proc(m::integer)::`Matrix`(rational);
    RandomFullRankMatrix(m, m)
end proc:

RandomPoint := proc(m::integer)::list(rational);
    RandomTools:-Generate(list(integer(range = -99..99), m))
end proc:

RandomPolynomial := proc(params::list(symbol), vars::list(symbol), deg::integer)::polynom;
    local p, v;
    p := ifelse(nops(params) = 0, rand(-99..99)(), randpoly(params, degree=deg));
    for v in vars do
        p := p + ifelse(nops(params) = 0, rand(-99..99)(), randpoly(params, degree=deg)) * v;
    end do;
    p
end proc:

RandomLinearMatrix := proc(m::integer, params::list(symbol), vars::list(symbol), deg::integer:=1)::`LinearMatrix`;
    Matrix(m, m, (i, j) -> RandomPolynomial(params, vars, deg), datatype = polynom)
end proc:
