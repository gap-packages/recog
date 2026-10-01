gap> START_TEST("gh-00492.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);

# Issue #492: over large fields the characteristic polynomial test almost never
# ruled out an invariant form, so RecogniseClassical often returned "unknown".
# See https://github.com/gap-packages/recog/issues/492
gap> i := 2;; Reset(GlobalRandomSource, i);; Reset(GlobalMersenneTwister, i);;
gap> RecogniseClassical(SL(6,257)).isSLContained;
true

# RECOG.RuleOutFormsByCharPoly must keep forms preserved up to a scalar
# lambda <> 1, and rule out both kinds of form for an element preserving none.
gap> RuleOut := function(G, g)
>      local f, r;
>      f := DefaultFieldOfMatrixGroup(G);
>      r := rec(d := DimensionOfMatrixGroup(G), q := Size(f),
>               p := Characteristic(f), a := DegreeOverPrimeField(f),
>               g := g, cpol := CharacteristicPolynomial(g),
>               maybeDual := true,
>               maybeFrobenius := IsEvenInt(DegreeOverPrimeField(f)));
>      RECOG.RuleOutFormsByCharPoly(r);
>      return [r.maybeDual, r.maybeFrobenius];
>    end;;
gap> Elms := G -> Concatenation(GeneratorsOfGroup(G),
>      ListX(GeneratorsOfGroup(G), GeneratorsOfGroup(G), \*));;
gap> G := Group(Concatenation(GeneratorsOfGroup(Sp(6,257)),
>      [DiagonalMat([3,3,3,1,1,1] * Z(257)^0)]));;
gap> ForAll(Elms(G), g -> RuleOut(G, g)[1]);
true
gap> G := Group(Concatenation(GeneratorsOfGroup(GU(4,257)),
>      [Z(257^2) * One(GU(4,257))]));;
gap> ForAll(Elms(G), g -> RuleOut(G, g)[2]);
true
gap> g := DiagonalMat([2,3,1,1,1,1/6] * Z(257)^0);;
gap> RuleOut(SL(6,257), g);
[ false, false ]
gap> RuleOut(SL(6,257^2), g);
[ false, false ]

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("gh-00492.tst");
