gap> START_TEST("on.tst");
gap> Reset(GlobalMersenneTwister, 1);;
gap> Reset(GlobalRandomSource, 1);;

# The standard generators of the orthogonal types preserve the standard
# form, have determinant 1 and generate Omega.
gap> CheckStdGens := function(type, d, q)
>     local f, std, J, e;
>     f := GF(q);
>     std := RECOG.ClassicalStandardGenerators(type, d, f).all;
>     J := RECOG.ClassicalStandardForm(type, d, f);
>     e := Position(RECOG.OrthogonalTypes, type);
>     e := [1, -1, 0][e];
>     return ForAll(std, g -> g * J * TransposedMat(g) = J
>                             and IsOne(DeterminantMat(g)))
>            and RECOG.FormOrthogonalType(RECOG.ClassicalForm(type, d, f),
>                                         IdentityMat(d, f)) = type
>            and Size(Group(std)) = Size(Omega(e, d, q));
> end;;
gap> ForAll([["O+", 4, 5], ["O+", 6, 3], ["O+", 8, 3], ["O-", 4, 5],
>            ["O-", 6, 3], ["O-", 8, 3], ["O-", 4, 9], ["O", 3, 7],
>            ["O", 5, 5], ["O", 7, 3], ["O", 5, 9]],
>           c -> CallFuncList(CheckStdGens, c));
true

# RECOG.ClassicalInvariantForm and RECOG.FormStandardBasis give a standard
# basis of a conjugate of Omega, from random spanning vectors; for odd
# degree the form must be the right multiple.
gap> CheckStdBasis := function(type, d, q)
>     local f, e, G, form, B;
>     f := GF(q);
>     e := Position(RECOG.OrthogonalTypes, type);
>     e := [1, -1, 0][e];
>     G := Omega(e, d, q)^RandomInvertibleMat(d, f);
>     form := RECOG.ClassicalInvariantForm(type, GeneratorsOfGroup(G), f);
>     B := RECOG.FormStandardBasis(form, RandomInvertibleMat(d, f));
>     return B <> fail
>            and RECOG.FormGram(form, B)
>                = RECOG.ClassicalStandardForm(type, d, f)
>            and RECOG.FormOrthogonalType(form, IdentityMat(d, f)) = type;
> end;;
gap> ForAll([1 .. 4], i -> ForAll([["O+", 6, 3], ["O+", 10, 25], ["O-", 4, 3],
>            ["O-", 8, 5], ["O-", 12, 9], ["O", 3, 3], ["O", 7, 5],
>            ["O", 9, 27], ["O", 11, 7]],
>           c -> CallFuncList(CheckStdBasis, c)));
true

# A hyperbolic pair is found also if the first two vectors span an
# anisotropic plane; an anisotropic plane has none.
gap> f := GF(7);;
gap> form := RECOG.ClassicalForm("O-", 4, f);;
gap> pair := RECOG.FormHyperbolicPair(form, IdentityMat(4, f){[3, 4, 1, 2]});;
gap> RECOG.FormGram(form, pair) = [[0, 1], [1, 0]] * One(f);
true
gap> RECOG.FormHyperbolicPair(form, IdentityMat(4, f){[3, 4]});
fail
gap> form := RECOG.ClassicalForm("O", 5, f);;
gap> e := IdentityMat(5, f);;
gap> pair := RECOG.FormHyperbolicPair(form,
>                [e[5], e[3] + Z(7) * e[4], e[1] + e[2]]);;
gap> RECOG.FormGram(form, pair) = [[0, 1], [1, 0]] * One(f);
true

# Lambda^2 of RECOG.O_KleinStandardPreimages are the standard generators of
# Omega^+(6,q), relative to the basis b_ij of the exterior square, and
# RECOG.O_KleinPreimage inverts Lambda^2 up to sign.
gap> CheckKlein := function(q)
>     local f, K, std, A, M;
>     f := GF(q);
>     K := RECOG.O_KleinBasis(IdentityMat(6, f));
>     std := RECOG.ClassicalStandardGenerators("O+", 6, f).all;
>     A := RECOG.O_KleinStandardPreimages(f);
>     if List(A, x -> RECOG.O_Wedge2(x, f)) <> List(std, x -> K * x * K^-1)
>        or not ForAll(A, x -> IsOne(DeterminantMat(x))) then
>         return false;
>     fi;
>     return ForAll([1 .. 5], function(i)
>         M := PseudoRandom(SL(4, q));
>         return RECOG.O_KleinPreimage(RECOG.O_Wedge2(M, f), f) in [M, -M];
>     end);
> end;;
gap> Filtered([3, 5, 7, 9, 25, 27], q -> not CheckKlein(q));
[  ]

# RECOG.O_FindStdGensOmega6 returns SLPs for the standard generators of
# Omega^+(6,q) relative to a standard basis of the given form, and
# RECOG.O_FinalDescent those of an Omega^+(6,q) in Omega^+-(8,q), whose
# basis starts with a standard basis of the restricted form, also for
# q = 3 mod 4, where no involution centraliser has the type it needs.
gap> CheckOmega6 := function(q)
>     local f, G, form, res, gens;
>     f := GF(q);
>     G := Omega(1, 6, q)^PseudoRandom(GL(6, f));
>     form := RECOG.ClassicalInvariantForm("O+", GeneratorsOfGroup(G), f);
>     res := RECOG.O_FindStdGensOmega6(GeneratorsOfGroup(G), form, f);
>     gens := ResultOfStraightLineProgram(res.slp, GeneratorsOfGroup(G));
>     return List(gens, g -> res.bas * g * res.bas^-1)
>            = RECOG.ClassicalStandardGenerators("O+", 6, f).all
>            and RECOG.FormGram(form, res.bas)
>                = RECOG.ClassicalStandardForm("O+", 6, f);
> end;;
gap> Filtered([3, 5, 7, 9, 11, 25, 27, 81], q -> not CheckOmega6(q));
[  ]
gap> CheckFinalDescent := function(e, q)
>     local f, G, form, res, gens, std;
>     f := GF(q);
>     G := Omega(e, 8, q)^PseudoRandom(GL(8, f));
>     form := RECOG.ClassicalInvariantForm("O+", GeneratorsOfGroup(G), f);
>     repeat
>         res := RECOG.O_FinalDescent(GeneratorsOfGroup(G), f, form,
>                                     RECOG.GoingDownRandomBound);
>     until res <> fail;
>     gens := ResultOfStraightLineProgram(res.slp, GeneratorsOfGroup(G));
>     std := RECOG.ClassicalStandardGenerators("O+", 6, f).all;
>     return List(gens, g -> res.bas * g * res.bas^-1)
>            = List(std, g -> DirectSumMat(g, IdentityMat(2, f)))
>            and RECOG.FormGram(form, res.bas{[1 .. 6]})
>                = RECOG.ClassicalStandardForm("O+", 6, f);
> end;;
gap> Filtered([[1, 3], [-1, 3], [1, 5], [-1, 5], [1, 7], [-1, 7], [1, 9],
>              [-1, 11], [1, 27]], c -> not CallFuncList(CheckFinalDescent, c));
[  ]

# RECOG.FindStdGens_O must express the standard generators of Omega(d,q)
# of RECOG.ClassicalStandardGenerators as straight line programs in the
# given generators, with respect to the basis it returns.
gap> CheckFindStdGens_O := function(e, d, q)
>     local f, G, res, gens, std, i;
>     f := GF(q);
>     G := Omega(e, d, q)^PseudoRandom(GL(d, f));
>     res := RECOG.FindStdGens_O(G);
>     gens := ResultOfStraightLineProgram(res.slpstd, GeneratorsOfGroup(G));
>     std := RECOG.ClassicalStandardGenerators(res.type, d, f).all;
>     for i in [1 .. Length(std)] do
>         if gens[i]^res.basi <> std[i] then
>             return Concatenation(res.type, "(", String(d), ",", String(q),
>                                  "): generator ", String(i), " is wrong");
>         fi;
>     od;
>     return res.type = RECOG.OrthogonalTypes[Position([1, -1, 0], e)];
> end;;
gap> List([[1, 8, 3], [-1, 8, 3], [1, 8, 5], [1, 8, 7], [-1, 8, 9],
>          [0, 9, 3], [0, 9, 5], [1, 10, 5], [-1, 10, 7], [0, 11, 9],
>          [1, 12, 3], [-1, 14, 3], [0, 13, 7], [1, 20, 11], [-1, 22, 5],
>          [0, 21, 27], [0, 35, 3]],
>         args -> CallFuncList(CheckFindStdGens_O, args));
[ true, true, true, true, true, true, true, true, true, true, true, true, 
  true, true, true, true, true ]

#
gap> STOP_TEST("on.tst");
