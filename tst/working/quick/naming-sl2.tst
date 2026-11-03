#
gap> START_TEST("naming-sl2.tst");
gap> oldInfoLevel := InfoLevel(InfoClassical);;
gap> SetInfoLevel(InfoClassical, 0);

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

# a subgroup of GammaL(1,q^2): the normaliser of a Singer cycle
gap> G := Group([[0*Z(37),Z(37)^19],[Z(37)^0,Z(37)^2]],
>               [[Z(37)^18,Z(37)^20],[0*Z(37),Z(37)^0]]);;
gap> r := RecogniseClassical(G);; [r.isSLContained, r.isSubgroupOfGammaL];
[ false, true ]

# imprimitive: the diagonal torus extended by the swap
gap> G := Group([[Z(37)^3,0*Z(37)],[0*Z(37),Z(37)^-3]],
>               [[0*Z(37),Z(37)^0],[Z(37)^0,0*Z(37)]]);;
gap> r := RecogniseClassical(G);; [r.isSLContained, r.isImprimitive];
[ false, true ]

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

#
gap> SetInfoLevel(InfoClassical, oldInfoLevel);
gap> STOP_TEST("naming-sl2.tst");
