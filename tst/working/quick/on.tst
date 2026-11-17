gap> START_TEST("on.tst");
gap> Reset(GlobalMersenneTwister, 1);;
gap> Reset(GlobalRandomSource, 1);;

# The standard generators of the orthogonal types preserve the standard
# form, also the quadratic form for q even, have determinant 1 and
# generate Omega.
gap> CheckStdGens := function(type, d, q)
>     local f, std, form, e;
>     f := GF(q);
>     std := RECOG.ClassicalStandardGenerators(type, d, f).all;
>     form := RECOG.ClassicalForm(type, d, f);
>     e := Position(RECOG.OrthogonalTypes, type);
>     e := [1, -1, 0][e];
>     return ForAll(std, g -> RECOG.FormRestriction(form, g) = form
>                             and IsOne(DeterminantMat(g)))
>            and RECOG.FormOrthogonalType(form, IdentityMat(d, f)) = type
>            and Size(Group(std)) = Size(Omega(e, d, q));
> end;;
gap> ForAll([["O+", 4, 5], ["O+", 6, 3], ["O+", 8, 3], ["O-", 4, 5],
>            ["O-", 6, 3], ["O-", 8, 3], ["O-", 4, 9], ["O", 3, 7],
>            ["O", 5, 5], ["O", 7, 3], ["O", 5, 9], ["O+", 4, 4],
>            ["O+", 6, 2], ["O+", 8, 2], ["O+", 6, 4], ["O-", 4, 2],
>            ["O-", 4, 4], ["O-", 6, 2], ["O-", 8, 2], ["O-", 4, 8],
>            ["O-", 6, 4]],
>           c -> CallFuncList(CheckStdGens, c));
true

# RECOG.ClassicalInvariantForm and RECOG.FormStandardBasis give a standard
# basis of a conjugate of Omega, from random spanning vectors; for odd
# degree the form must be the right multiple, and for q even the basis is
# standard for the quadratic form.
gap> CheckStdBasis := function(type, d, q)
>     local f, e, G, form, B;
>     f := GF(q);
>     e := Position(RECOG.OrthogonalTypes, type);
>     e := [1, -1, 0][e];
>     G := Omega(e, d, q)^RandomInvertibleMat(d, f);
>     form := RECOG.ClassicalInvariantForm(type, GeneratorsOfGroup(G), f);
>     B := RECOG.FormStandardBasis(form, RandomInvertibleMat(d, f));
>     return B <> fail
>            and RECOG.FormRestriction(form, B)
>                = RECOG.ClassicalForm(type, d, f)
>            and RECOG.FormOrthogonalType(form, IdentityMat(d, f)) = type;
> end;;
gap> ForAll([1 .. 4], i -> ForAll([["O+", 6, 3], ["O+", 10, 25], ["O-", 4, 3],
>            ["O-", 8, 5], ["O-", 12, 9], ["O", 3, 3], ["O", 7, 5],
>            ["O", 9, 27], ["O", 11, 7], ["O+", 6, 2], ["O+", 10, 4],
>            ["O-", 4, 2], ["O-", 8, 8], ["O-", 12, 4], ["O+", 8, 64],
>            ["O-", 6, 256]],
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

# For q even, the pair is singular for the quadratic form, also in a
# hyperbolic plane spanned by a non-singular and a singular vector
gap> f := GF(4);;
gap> form := RECOG.ClassicalForm("O-", 4, f);;
gap> e := IdentityMat(4, f);;
gap> pair := RECOG.FormHyperbolicPair(form, [e[1] + e[3], e[2]]);;
gap> RECOG.FormRestriction(form, pair) = RECOG.ClassicalForm("O+", 2, f);
true
gap> RECOG.FormHyperbolicPair(form, [e[3], e[4]]);
fail

# Lambda^2 of RECOG.Omega_KleinStandardPreimages are the standard generators of
# Omega^+(6,q), relative to the basis b_ij of the exterior square, and
# RECOG.Omega_KleinPreimage inverts Lambda^2 up to sign.
gap> CheckKlein := function(q)
>     local f, K, std, A, M;
>     f := GF(q);
>     K := RECOG.Omega_KleinBasis(IdentityMat(6, f));
>     std := RECOG.ClassicalStandardGenerators("O+", 6, f).all;
>     A := RECOG.Omega_KleinStandardPreimages(f);
>     if List(A, x -> RECOG.Omega_Wedge2(x, f)) <> List(std, x -> K * x * K^-1)
>        or not ForAll(A, x -> IsOne(DeterminantMat(x))) then
>         return false;
>     fi;
>     return ForAll([1 .. 5], function(i)
>         M := PseudoRandom(SL(4, q));
>         return RECOG.Omega_KleinPreimage(RECOG.Omega_Wedge2(M, f), f)
>                in [M, -M];
>     end);
> end;;
gap> Filtered([2, 3, 4, 5, 7, 8, 9, 25, 27], q -> not CheckKlein(q));
[  ]

# RECOG.FindStdGensOmega6 returns SLPs for the standard generators of
# Omega^+(6,q) relative to a standard basis of the given form, and
# RECOG.Omega_FinalDescent those of an Omega^+(6,q) in Omega^+-(8,q), whose
# basis starts with a standard basis of the restricted form, also for
# q = 3 mod 4, where no involution centraliser has the type it needs, and
# for q even, by an element of odd order instead of an involution, resp. a
# stabiliser chain for q = 2.
gap> CheckOmega6 := function(q)
>     local f, G, form, res, gens;
>     f := GF(q);
>     G := Omega(1, 6, q)^PseudoRandom(GL(6, f));
>     form := RECOG.ClassicalInvariantForm("O+", GeneratorsOfGroup(G), f);
>     res := RECOG.FindStdGensOmega6(GeneratorsOfGroup(G), form, f);
>     gens := ResultOfStraightLineProgram(res.slp, GeneratorsOfGroup(G));
>     return List(gens, g -> res.bas * g * res.bas^-1)
>            = RECOG.ClassicalStandardGenerators("O+", 6, f).all
>            and RECOG.FormRestriction(form, res.bas)
>                = RECOG.ClassicalForm("O+", 6, f);
> end;;
gap> Filtered([2, 3, 4, 5, 7, 8, 9, 11, 16, 25, 27, 81],
>             q -> not CheckOmega6(q));
[  ]
gap> CheckFinalDescent := function(e, q)
>     local f, G, form, res, gens, std;
>     f := GF(q);
>     G := Omega(e, 8, q)^PseudoRandom(GL(8, f));
>     form := RECOG.ClassicalInvariantForm("O+", GeneratorsOfGroup(G), f);
>     repeat
>         res := RECOG.Omega_FinalDescent(GeneratorsOfGroup(G), f, form,
>                                     RECOG.GoingDownRandomBound);
>     until res <> fail;
>     gens := ResultOfStraightLineProgram(res.slp, GeneratorsOfGroup(G));
>     std := RECOG.ClassicalStandardGenerators("O+", 6, f).all;
>     return List(gens, g -> res.bas * g * res.bas^-1)
>            = List(std, g -> DirectSumMat(g, IdentityMat(2, f)))
>            and RECOG.FormRestriction(form, res.bas{[1 .. 6]})
>                = RECOG.ClassicalForm("O+", 6, f);
> end;;
gap> Filtered([[1, 3], [-1, 3], [1, 5], [-1, 5], [1, 7], [-1, 7], [1, 9],
>              [-1, 11], [1, 27], [1, 2], [-1, 2], [1, 4], [-1, 4], [1, 8],
>              [-1, 16]], c -> not CallFuncList(CheckFinalDescent, c));
[  ]

# RECOG.FindStdGens_Omega must express the standard generators of Omega(d,q)
# of RECOG.ClassicalStandardGenerators as straight line programs in the
# given generators, with respect to the basis it returns.
gap> CheckFindStdGens_Omega := function(e, d, q)
>     local f, G, res, gens, std, i;
>     f := GF(q);
>     G := Omega(e, d, q)^PseudoRandom(GL(d, f));
>     res := RECOG.FindStdGens_Omega(G);
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
>         args -> CallFuncList(CheckFindStdGens_Omega, args));
[ true, true, true, true, true, true, true, true, true, true, true, true, 
  true, true, true, true, true ]
gap> List([[1, 8, 2], [-1, 8, 2], [1, 8, 4], [-1, 8, 4], [1, 10, 2],
>          [-1, 12, 4], [1, 16, 8], [-1, 22, 2], [1, 20, 16]],
>         args -> CallFuncList(CheckFindStdGens_Omega, args));
[ true, true, true, true, true, true, true, true, true ]

# RECOG.Form_Rewrite must return an SLP in the standard generators for
# elements of the standard copy
gap> CheckForm_Rewrite := function(type, d, q)
>     local f, W, std, G, els;
>     f := GF(q);
>     W := RECOG.Form_RewriteSetup(type, d, f);
>     std := RECOG.ClassicalStandardGenerators(type, d, f);
>     G := Group(std.all);
>     els := Concatenation(List([1 .. 4], i -> PseudoRandom(G)), std.all,
>                          [One(G), std.s^std.v, std.delta^std.all[4]]);
>     return ForAll(els, g -> ResultOfStraightLineProgram(
>                                 RECOG.Form_Rewrite(W, g), std.all) = g);
> end;;
gap> ForAll([["O+", 8, 3], ["O+", 10, 5], ["O+", 8, 9], ["O-", 8, 3],
>            ["O-", 10, 5], ["O-", 8, 9], ["O", 9, 3], ["O", 11, 5],
>            ["O", 9, 9], ["O+", 8, 2], ["O+", 10, 4], ["O-", 8, 2],
>            ["O-", 10, 4], ["O-", 8, 8], ["O-", 6, 16]],
>           c -> CallFuncList(CheckForm_Rewrite, c));
true

# The spinor norm is trivial on Omega, multiplicative, and trivial on -1
# exactly if q^m = eps mod 4
gap> FormOf := G -> rec( gram := InvariantBilinearForm(G).matrix, frob := 1,
>                        field := FieldOfMatrixGroup(G) );;
gap> form := FormOf(SO(1, 8, 5));;
gap> xs := List([1 .. 10], i -> PseudoRandom(SO(1, 8, 5)));;
gap> ForAll(GeneratorsOfGroup(Omega(1, 8, 5)), g -> RECOG.HasTrivialSpinorNorm(
>        g, FormOf(Omega(1, 8, 5))));
true
gap> ForAll([1 .. 9], i -> RECOG.HasTrivialSpinorNorm(xs[i] * xs[i + 1], form)
>        = (RECOG.HasTrivialSpinorNorm(xs[i], form)
>           = RECOG.HasTrivialSpinorNorm(xs[i + 1], form)));
true
gap> List([[1, 8, 3], [-1, 8, 3], [1, 10, 3], [-1, 10, 3]], c ->
>        RECOG.HasTrivialSpinorNorm(-IdentityMat(c[2], GF(c[3])),
>            FormOf(Omega(c[1], c[2], c[3]))));
[ true, false, false, true ]

# Squares are those of the field of the form: -1 on a hyperbolic pair has
# spinor norm -1, a square in GF(9), also as a matrix over GF(3)
gap> RECOG.HasTrivialSpinorNorm(DiagonalMat([-1, -1, 1, 1, 1, 1, 1, 1] * Z(3)^0),
>        RECOG.ClassicalForm("O+", 8, GF(9)));
true

# On all of GO the spinor norm is a homomorphism, and on the reflection in
# v it is beta(v,v)/2 mod squares
gap> form := FormOf(GO(9, 3));;
gap> Refl := v -> One(form.gram)
>        - (2 / (v * form.gram * v)) * TransposedMat([form.gram * v]) * [v];;
gap> vs := Filtered(List([1 .. 20], i -> Random(GF(3)^9)),
>        v -> not IsZero(v * form.gram * v));;
gap> ForAll(vs, v -> (RECOG.SpinorNorm(Refl(v), form) = 0)
>        = RECOG.IsSquareFFE(v * form.gram * v / 2, 3));
true
gap> xs := List([1 .. 10], i -> PseudoRandom(GO(9, 3)));;
gap> ForAll([1 .. 9], i -> RECOG.SpinorNorm(xs[i] * xs[i + 1], form)
>        = (RECOG.SpinorNorm(xs[i], form)
>           + RECOG.SpinorNorm(xs[i + 1], form)) mod 2);
true

# For q even, Omega is the kernel of the Dickson invariant on the isometries
# of the quadratic form; the transvection swapping e_1 and f_1 is one
gap> ForAll(GeneratorsOfGroup(Omega(-1, 8, 4)),
>           RECOG.HasTrivialDicksonInvariant);
true
gap> form := RECOG.ClassicalForm("O+", 8, GF(4));;
gap> x := RECOG.EmbedBlock(8, GF(4), [1, 2], [[0, 1], [1, 0]]);;
gap> [RECOG.PreservesQuadraticForm(x, form),
>     RECOG.HasTrivialDicksonInvariant(x)];
[ true, false ]
gap> x := RECOG.EmbedBlock(8, GF(4), [1, 2], [[1, 1], [0, 1]]);;
gap> RECOG.PreservesQuadraticForm(x, form);
false

# ClassicalNatural makes natural Omega(d,q) a POmega leaf, also with
# scalars on the generators, and its SLPs accept any scalar, also from a
# larger field, and matrices over GF(9) with entries in GF(3), but no
# element of Omega(9,9). SO(9,3) is no leaf: it is Omega(9,3) extended by
# an element of spinor norm -1.
gap> Leaf := function(ri)
>     if not IsLeaf(ri) then
>         ri := ImageRecogNode(ri);
>     fi;
>     return ri;
> end;;
gap> IsScalarMultiple := function(x, y)
>     local pos;
>     pos := PositionNonZero(y[1]);
>     return x = x[1, pos] / y[1, pos] * y;
> end;;
gap> g := PseudoRandom(GL(9, 3));;
gap> S := Omega(9, 3)^g;;
gap> ri := Leaf(RECOG.TestGroup(S, false, Size(S)));;
gap> ri!.fhmethsel.successMethod;
"ClassicalNatural"
gap> ForAll([1 .. 5], function(i)
>     local x;
>     x := PseudoRandom(S);
>     return IsScalarMultiple(ResultOfStraightLineProgram(
>                SLPforElement(ri, Z(9)^i * x), NiceGens(ri)), x);
> end);
true
gap> SLPforElement(ri, PseudoRandom(Omega(9, 9))^g);
fail
gap> x := PseudoRandom(S);;
gap> IsScalarMultiple(ResultOfStraightLineProgram(
>        SLPforElement(ri, ImmutableMatrix(GF(9), x)), NiceGens(ri)), x);
true
gap> S := Omega(1, 10, 3)^PseudoRandom(GL(10, 3));;
gap> Leaf(RECOG.TestGroup(S, false, Size(S)))!.fhmethsel.successMethod;
"ClassicalNatural"
gap> G := Group(List(GeneratorsOfGroup(Omega(-1, 8, 5)),
>                    x -> Z(5)^Random([0 .. 3]) * x));;
gap> Leaf(RECOG.TestGroup(G, true, Size(Omega(-1, 8, 5))))!.fhmethsel.successMethod;
"ClassicalNatural"
gap> ri := Leaf(RECOG.TestGroup(SO(9, 3), false, Size(SO(9, 3))));;
gap> [ri!.fhmethsel.successMethod, Size(ImageRecogNode(ri)),
>    KernelRecogNode(ri)!.fhmethsel.successMethod];
[ "ClassicalNatural", 2, "ClassicalNatural" ]
gap> [SLPforElement(ri, PseudoRandom(GL(9, 3))),
>     SLPforElement(ri, PseudoRandom(GL(9, 9)))];
[ fail, fail ]

# Like the leaf, the quotient node above it accepts scalars from a larger
# field and matrices over GF(9) with entries in GF(3)
gap> x := PseudoRandom(SO(9, 3));;
gap> ForAll([Z(9) * x, ImmutableMatrix(GF(9), x)], y -> IsScalarMultiple(
>        ResultOfStraightLineProgram(SLPforElement(ri, y), NiceGens(ri)), x));
true

# In even dimension the first quotient is mu mod squares and det / mu^(d/2),
# with kernel PSO: GO-(10,5) has elements of determinant -1, a 10th power
# in GF(5), which ProjDeterminant misses. The spinor norm follows if -1
# lies in Omega, as in GO+(10,5) and SO+(8,3). GO(9,3) needs the sign that
# makes the determinant 1. RecogniseClassical is inconclusive in about one
# run in 500, which sends the group to StabilizerChainProj; resetting the
# random sources gives each group the same seed in every GAP version.
gap> Split := function(ri)
>     if IsLeaf(ri) then
>         return ri!.fhmethsel.successMethod;
>     fi;
>     return [ri!.fhmethsel.successMethod, Size(ImageRecogNode(ri)),
>             Split(KernelRecogNode(ri))];
> end;;
gap> for G in [GO(9, 3), GO(-1, 10, 5), GO(1, 10, 5), SO(1, 8, 3)] do
>     Reset(GlobalMersenneTwister, 1);
>     Reset(GlobalRandomSource, 1);
>     Print(Split(Leaf(RECOG.TestGroup(G, false, Size(G)))), "\n");
> od;
[ "ClassicalNatural", 2, "ClassicalNatural" ]
[ "ClassicalNatural", 2, "ClassicalNatural" ]
[ "ClassicalNatural", 2, [ "ClassicalNatural", 2, "ClassicalNatural" ] ]
[ "ClassicalNatural", 2, "ClassicalNatural" ]

# The same for q even, where O^+(10,2) extends Omega^+(10,2) by an element
# of Dickson invariant 1
gap> g := PseudoRandom(GL(8, 4));;
gap> S := Omega(-1, 8, 4)^g;;
gap> ri := Leaf(RECOG.TestGroup(S, false, Size(S)));;
gap> ri!.fhmethsel.successMethod;
"ClassicalNatural"
gap> ForAll([1 .. 5], function(i)
>     local x;
>     x := PseudoRandom(S);
>     return IsScalarMultiple(ResultOfStraightLineProgram(
>                SLPforElement(ri, Z(16)^i * x), NiceGens(ri)), x);
> end);
true
gap> SLPforElement(ri, PseudoRandom(Sp(8, 4))^g);
fail
gap> S := Omega(1, 10, 2)^PseudoRandom(GL(10, 2));;
gap> Leaf(RECOG.TestGroup(S, false, Size(S)))!.fhmethsel.successMethod;
"ClassicalNatural"
gap> G := Group(List(GeneratorsOfGroup(Omega(1, 8, 4)),
>                    x -> Z(4)^Random([0 .. 2]) * x));;
gap> Leaf(RECOG.TestGroup(G, true, Size(Omega(1, 8, 4))))!.fhmethsel.successMethod;
"ClassicalNatural"
gap> Leaf(RECOG.TestGroup(GO(1, 10, 2), false, Size(GO(1, 10, 2))))!.fhmethsel.successMethod;
"StabilizerChainProj"

#
gap> STOP_TEST("on.tst");
