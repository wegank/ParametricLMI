interface(errorbreak=3):
kernelopts(assertlevel=1):

ReadFromFile := proc(fname::string)::list;
    local f, data, line;
    f := fopen(fname, READ);
    data := [];
    while not feof(f) do
        line := readline(f);
        if line = 0 then
            next;
        end if;
        data := [op(data), map(parse, StringTools:-Split(line, ","))];
    end do;
    fclose(f);
    data
end proc:

TimeQE1 := proc(fname::string)::double;
    local data, vars, A, m, g, Phi, g_i, t0, t1;
    data := ReadFromFile(fname);
    vars := data[1];
    A := Matrix(data[2..-1]);
    m := LinearAlgebra:-RowDimension(A);
    g := PolynomialTools:-CoefficientList(expand(LinearAlgebra:-Determinant(A + t * LinearAlgebra:-IdentityMatrix(m))), t);
    Phi := true;
    for g_i in g do
        Phi := And(Phi, g_i >= 0);
    end do;
    Phi := exists(vars, Phi);
    t0 := time();
    Phi := QuantifierElimination:-QuantifierEliminate(Phi);
    t1 := time();
    t1 - t0
end proc:

read("src/solvelmi.mpl"):

TimeO1 := proc(fname::string)::double;
    local data, vars, params, A, Phi, t0, t1;
    data := ReadFromFile(fname);
    vars := data[1];
    A := Matrix(data[2..-1]);
    params := convert(indets(A) minus convert(vars, set), list);
    A := LinearMatrix(A, params, vars);
    t0 := time();
    Phi := ParametricSolveLMI(A):
    t1 := time();
    t1 - t0
end proc:

# Example usage:
# TimeQE1("examples/data/mkn11.dat");
