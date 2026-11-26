gap> START_TEST("goingdown.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);
gap> Reset(GlobalMersenneTwister, 1);;
gap> Reset(GlobalRandomSource, 1);;

# RECOG.FindStingrayElement returns m-stingray elements: s fixes a
# subspace of codimension m and its characteristic polynomial is
# (x-1)^(d-m) times an irreducible polynomial of degree m.
gap> IsStingray := function(s, m)
>     local cp;
>     s := StripMemory(s);
>     cp := Collected(Factors(CharacteristicPolynomial(s)));
>     return Length(RECOG.FixspaceMat(s)) = NrRows(s) - m and Length(cp) = 2
>            and ForAny(cp, c -> Degree(c[1]) = m and c[2] = 1);
> end;;
gap> params := RECOG.GoingDownParameters("SL", 7);;
gap> D := RECOG.StingrayBodyDimensions(30, params);
[ 2 .. 10 ]
gap> G := GroupWithMemory(SL(30, 7));;
gap> ForAll([1..10], function(i)
>      local r;
>      r := RECOG.FindStingrayElement(G, D, 100);
>      return r <> fail and r.dim in D and IsStingray(r.element, r.dim);
>    end);
true

# RECOG.StingrayFactor agrees with the test on the full factorisation, for
# blocks of several sizes and for q > 2^16.
gap> StingrayFactorByFactors := function(chi, F, D)
>     local q, p, x, fs, i, m, others, c, B, gamma;
>     q := Size(F);
>     p := Characteristic(F);
>     x := Indeterminate(F);
>     fs := Collected(Factors(PolynomialRing(F), chi));
>     SortBy(fs, f -> Degree(f[1]));
>     for i in [1..Length(fs)] do
>         m := Degree(fs[i][1]);
>         if fs[i][2] <> 1 or not m in D or
>            ForAny([1..Length(fs)], j -> j <> i and Degree(fs[j][1]) mod m = 0) then
>             continue;
>         fi;
>         others := fs{Difference([1..Length(fs)], [i])};
>         c := Maximum(Concatenation([1], List(others, f -> f[2])));
>         B := p^LogInt(p * c - 1, p)
>              * Lcm(Concatenation([1], List(others, f -> q^Degree(f[1]) - 1)));
>         gamma := PowerMod(x, B, fs[i][1]);
>         if ForAll(PrimeDivisors(m),
>                   r -> PowerMod(gamma, q^(m/r), fs[i][1]) <> gamma) then
>             return rec( P := fs[i][1], B := B );
>         fi;
>     od;
>     return fail;
> end;;
gap> CheckStingrayFactor := function(type, G)
>     local F, D, block, ok, i, chi;
>     F := DefaultFieldOfMatrixGroup(G);
>     D := RECOG.StingrayBodyDimensions(DimensionOfMatrixGroup(G),
>                                       RECOG.GoingDownParameters(type, Size(F)));
>     block := RECOG.StingrayDegreeBlock;
>     ok := ForAll([1..20], function(i)
>         chi := CharacteristicPolynomial(F, F, PseudoRandom(G));
>         return ForAll([1, 3, 16], function(b)
>             RECOG.StingrayDegreeBlock := b;
>             return RECOG.StingrayFactor(chi, F, D)
>                    = StingrayFactorByFactors(chi, F, D);
>         end);
>     end);
>     RECOG.StingrayDegreeBlock := block;
>     return ok;
> end;;
gap> ForAll([["SL", SL(24, 3)], ["SL", SL(16, 4)], ["SL", SL(30, 2)],
>            ["SL", SL(12, 25)], ["SL", SL(8, 2^17)], ["SU", SU(14, 3)],
>            ["Sp", Sp(24, 3)], ["Sp", Sp(20, 4)], ["O+", Omega(1, 24, 3)],
>            ["O-", Omega(-1, 22, 5)], ["O", Omega(25, 3)],
>            ["O+", Omega(1, 20, 2)]],
>           c -> CallFuncList(CheckStingrayFactor, c));
true

# RECOG.GoingDown returns SLPs for generators of the terminal group, SL(4,q),
# Sp(8,q), SU(6,q), SU(10,2) or Omega^+-(8,q), also for Sp with q even, and
# a basis in which their lifts are block diagonal with an identity block.
gap> CheckGoingDown := function(type, d, q)
>     local G, F, t, down, x;
>     if type = "SL" then
>         G := SL(d, q);
>     elif type = "Sp" then
>         G := Sp(d, q);
>     elif type = "SU" then
>         G := SU(d, q);
>     else
>         G := Omega([1, -1, 0][Position(RECOG.OrthogonalTypes, type)], d, q);
>     fi;
>     F := DefaultFieldOfMatrixGroup(G);
>     t := RECOG.GoingDownParameters(type, Size(F)).terminal;
>     G := GroupWithMemory(G^PseudoRandom(GL(d, F)));
>     down := RECOG.GoingDown(G, type, RECOG.GoingDownRandomBound);
>     x := ResultOfStraightLineProgram(down.slp,
>                                      StripMemory(GeneratorsOfGroup(G)));
>     return Length(down.gens[1]) = t and
>            ForAll([1..Length(x)], i -> down.bas * x[i] * down.bas^-1
>                = DirectSumMat(down.gens[i], IdentityMat(d - t, F)));
> end;;
gap> List([["SL", 5, 2], ["SL", 9, 3], ["SL", 20, 5], ["SL", 33, 4],
>          ["SL", 40, 121], ["Sp", 10, 3], ["Sp", 20, 5], ["Sp", 30, 9],
>          ["Sp", 10, 2], ["Sp", 16, 4]],
>         args -> CallFuncList(CheckGoingDown, args));
[ true, true, true, true, true, true, true, true, true, true ]
gap> List([["SU", 7, 3], ["SU", 12, 4], ["SU", 15, 5], ["SU", 11, 2],
>          ["SU", 20, 9]],
>         args -> CallFuncList(CheckGoingDown, args));
[ true, true, true, true, true ]
gap> List([["O+", 10, 3], ["O-", 12, 5], ["O", 9, 3], ["O", 13, 7],
>          ["O+", 20, 9], ["O-", 30, 3], ["O+", 10, 2], ["O-", 12, 4],
>          ["O+", 16, 8]],
>         args -> CallFuncList(CheckGoingDown, args));
[ true, true, true, true, true, true, true, true, true ]

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("goingdown.tst");
