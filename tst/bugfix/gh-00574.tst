gap> START_TEST("gh-00574.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);

# Issue #574: on a conjugate of SL(2,8) that is not writable over GF(8),
# RecogniseProjectiveGroup did not terminate. The element orders 7 and 9
# divide 511 and 513, so the order-based d = 2 naming took the group for
# SL(2,512), and the SL2 leaf then looped.
# See https://github.com/gap-packages/recog/issues/574
gap> z := Z(512);;
gap> c := [[One(z), z], [Zero(z), One(z)]];;
gap> u := GeneratorsOfGroup(SL(2,8));;
gap> H := Group(u[1]^c, (u[1]*u[2])^c);;
gap> FieldOfMatrixGroup(H);
GF(2^9)
gap> RecogniseClassical(H).isSLContained;
false
gap> ri := RECOG.TestGroup(H, true, 504);;
gap> IsReady(ri);
true

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("gh-00574.tst");
