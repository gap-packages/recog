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

#
gap> STOP_TEST("on.tst");
