gap> START_TEST("ClassicalSubfieldCharPoly.tst");

# An element of Sp(2,9) x Sp(2,9) with eigenvalues all four primitive 5th
# roots of unity. Its characteristic polynomial x^4+x^3+x^2+x+1 has
# coefficients in GF(3), where it is irreducible; over GF(9) it is the
# product of two distinct quadratics.
gap> F := GF(9);;
gap> t := First(Elements(F), t -> t^2 + t - 1 = Zero(F));;
gap> a := [[0, -1], [1, t]] * One(F);;
gap> g := DirectSumMat(a, a^2);;
gap> Order(g);
5
gap> List(Factors(PolynomialRing(F), CharacteristicPolynomial(g)), Degree);
[ 2, 2 ]

# g is a large ppd(4,9;2)-element
gap> IsPpdElementD2(F, g, 4, 9, 1);
[ 2, true, 16 ]

# g fixes 2-dimensional subspaces, so it must not prove irreducibility
gap> r := rec(d := 4, field := F, cpol := CharacteristicPolynomial(g),
>             dimsReducible := [], isReducible := "unknown");;
gap> FindHomMethodsClassical.IsReducible(r) = TemporaryFailure;
true
gap> r.dimsReducible;
[ 0, 2, 4 ]

# Every non-identity element of <g> is a large special ppd(4,9;2)-element,
# the witness NonGenericSymplectic needs for Sp(4,9). TestRandomElement only
# looks for them once needE2 is set, so set it and draw elements by hand.
gap> Reset(GlobalRandomSource, 1);; Reset(GlobalMersenneTwister, 1);;
gap> r := RecogniseClassical(Group(g), rec(case := "symplectic"));;
gap> r.needE2 := true;;
gap> for i in [1 .. 10] do FindHomMethodsClassical.TestRandomElement(r); od;
gap> r.LS;
[ 2 ]

#
gap> STOP_TEST("ClassicalSubfieldCharPoly.tst");
