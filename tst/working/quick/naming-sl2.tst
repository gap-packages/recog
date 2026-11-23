#
gap> START_TEST("naming-sl2.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog_ClassicalNaming);;
gap> SetInfoLevel(InfoRecog_ClassicalNaming, 0);

# Issue #345: RecogniseClassical used to leave isSLContained at "unknown" for
# every degree-2 group.
gap> List([2,3,4,5,7,8,9,11,13,25,27,37],
>         q -> RecogniseClassical(SL(2,q)).isSLContained);
[ true, true, true, true, true, true, true, true, true, true, true, true ]

# GL(2,q) contains SL(2,q), so naming must say so too
gap> List([2,3,4,5,7,8,9,11,13,25,27,37],
>         q -> RecogniseClassical(GL(2,q)).isSLContained);
[ true, true, true, true, true, true, true, true, true, true, true, true ]

# Sp(2,q) = SL(2,q)
gap> RecogniseClassical(SL(2,37)).isSpContained;
true

# One group per class that gets ruled out. Each must give a definite false, not
# "unknown", and must be rejected by the class it belongs to.

# reducible: a Borel subgroup
gap> RecogniseClassical(Group([[Z(37),Z(37)^0],[0*Z(37),Z(37)]])).isSLContained;
false

# abelian: a Singer cycle, which is irreducible, so IsAbelian decides it rather
# than MeatAxe
gap> G := Group([[0*Z(37),Z(37)^19],[Z(37)^0,Z(37)^2]]);;
gap> r := RecogniseClassical(G);; [r.isSLContained, r.isAbelian];
[ false, true ]

# exp(G/Z) = 2: the quaternion group inside SL(2,37)
gap> G := Group([[Z(37)^9,0*Z(37)],[0*Z(37),Z(37)^27]],
>               [[0*Z(37),Z(37)^0],[Z(37)^18,0*Z(37)]]);;
gap> r := RecogniseClassical(G);; [r.isSLContained, r.hasExp2];
[ false, true ]

# Generators with scalar squares need not give exponent 2 modulo scalars:
# these three generate GL(2,9)
gap> z := Z(9);;
gap> r := rec(n := 16, hasExp2 := "unknown", h := fail, q := 9,
>             generators := [[[1,1],[0,2]]*Z(3)^0, [[z^3,z^2],[z^7,z^7]],
>                            [[0*z,2*z^0],[z^5,0*z]]]);;
gap> List(r.generators, g -> RECOG.IsScalarMat(g^2));
[ true, true, true ]
gap> FindHomMethodsClassical.ExponentTwoModScalars(r) = NeverApplicable;
true
gap> r.hasExp2;
false

# a subgroup of GammaL(1,q^2): the normaliser of a Singer cycle
gap> G := Group([[0*Z(37),Z(37)^19],[Z(37)^0,Z(37)^2]],
>               [[Z(37)^18,Z(37)^20],[0*Z(37),Z(37)^0]]);;
gap> r := RecogniseClassical(G);; [r.isSLContained, r.isSubgroupOfGammaL];
[ false, true ]

# In GammaL(1,q^2), h^2 lies in the Singer torus, whose non-scalar elements
# have irreducible characteristic polynomial over GF(q). Here h^2 = diag(i,-i)
# has x^2+1, irreducible over GF(3) but not over GF(9), so h proves SL(2,9) is
# not in GammaL(1,81).
gap> r := rec(d := 2, q := 9, field := GF(9), h := DiagonalMat([Z(9), Z(9)^-1]),
>             generators := GeneratorsOfGroup(SL(2,9)),
>             isSubgroupOfGammaL := "unknown");;
gap> FindHomMethodsClassical.IsSubgroupOfGammaL(r) = NeverApplicable;
true
gap> r.isSubgroupOfGammaL;
false

# GammaL(1,49): q^2-1 = 48 has no primitive prime divisor, which the test
# must not need
gap> G := Group([[0*Z(7),Z(7)^4],[Z(7)^0,Z(7)^0]],
>               [[Z(7)^2,Z(7)^0],[Z(7)^2,Z(7)^5]]);;
gap> Size(G);
96
gap> r := RecogniseClassical(G);; [r.isSLContained, r.isSubgroupOfGammaL];
[ false, true ]

# imprimitive: the diagonal torus extended by the swap
gap> G := Group([[Z(37)^3,0*Z(37)],[0*Z(37),Z(37)^-3]],
>               [[0*Z(37),Z(37)^0],[Z(37)^0,0*Z(37)]]);;
gap> r := RecogniseClassical(G);; [r.isSLContained, r.isImprimitive];
[ false, true ]

# the same group permuting two lines other than the coordinate axes
gap> G := G^([[1,2],[3,5]] * Z(37)^0);;
gap> r := RecogniseClassical(G);; [r.isSLContained, r.isImprimitive];
[ false, true ]

# RecogniseSL2Natural loops on this group, so RecogniseGroup relies on that
gap> oldRecogLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);
gap> Size(RecogniseGroup(G));
24
gap> SetInfoLevel(InfoRecog, oldRecogLevel);

# 2.Alt(5) inside SL(2,11). This used to come out true: the Alt(5) test only
# fired when the projective group moved at most 5 points, but it acts on the
# q+1 = 12 points of the projective line, and is transitive on them.
gap> G := Group([[0*Z(11),Z(11)],[Z(11)^4,0*Z(11)]],
>               [[0*Z(11),Z(11)^5],[Z(11)^0,Z(11)^5]]);;
gap> Size(G);
120
gap> r := RecogniseClassical(G);; [r.isSLContained, r.isAlt5Alt4Sym4];
[ false, true ]

# representable over a proper subfield: SL(2,7) inside GL(2,49). Not SL(2,5),
# whose projective image is Alt(5) and which the previous test catches first.
gap> G := Group([[Z(7^2)^30,Z(7^2)],[Z(7^2)^13,Z(7^2)^47]],
>               [[Z(7^2)^29,Z(7^2)^7],[Z(7)^2,Z(7^2)]]);;
gap> FieldOfMatrixGroup(G);
GF(7^2)
gap> r := RecogniseClassical(G);; [r.isSLContained, r.isRepresentableOverSubfield];
[ false, true ]

# Large q: nothing may enumerate the q+1 points of the projective line
gap> RecogniseClassical(SL(2,2^20)).isSLContained;
true
gap> RecogniseClassical(GL(2,3^13)).isSLContained;
true

# beyond RECOG.Degree2LineEnumerationLimit a subfield group stays undecided
gap> x := [[Z(2^20)^0, Z(2^20)], [0*Z(2), Z(2)^0]];;
gap> G := Group(List(GeneratorsOfGroup(SL(2,2^10)), g -> g^x));;
gap> FieldOfMatrixGroup(G);
GF(2^20)
gap> RecogniseClassical(G).isSLContained;
"unknown"

#
gap> SetInfoLevel(InfoRecog_ClassicalNaming, oldInfoLevel);
gap> STOP_TEST("naming-sl2.tst");
