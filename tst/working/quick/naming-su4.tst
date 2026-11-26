#
gap> START_TEST("naming-su4.tst");

# 2.A7 < SU(4,47), from the ATLAS generators over Z[b7], b7^2 + b7 + 2 = 0.
# Its element orders have no prime above 7, but q-1 = 2^5*3*23 for q = 47^2,
# so a scalar of order 23 puts the prime 23 into every matrix order.
gap> F := GF(47^2);;
gap> b7 := RootsOfPolynomial(F, Indeterminate(F)^2 + Indeterminate(F) + 2)[1];;
gap> H := Group(One(F) * [[0, 1, 0, 0], [-1, -1, 0, 0], [0, 0, 0, 1], [0, 0, -1, -1]],
>               [[0, 1, 0, 0], [0, 0, 1, 0], [0, -b7-1, -1, -1], [1, 1, -b7, 0]]
>               * One(F));;
gap> Size(H);
5040
gap> HZ := Group(Concatenation(GeneratorsOfGroup(H), [Z(47^2) * One(H)]));;
gap> ForAny([1 .. 10], i -> RecogniseClassical(HZ).isSUContained = true);
false

# SU(4,47) with scalars is still named
gap> G := Group(Concatenation(GeneratorsOfGroup(SU(4, 47)), [Z(47^2) * One(HZ)]));;
gap> ForAll([1 .. 5], i -> RecogniseClassical(G).isSUContained = true);
true

#
gap> STOP_TEST("naming-su4.tst");
