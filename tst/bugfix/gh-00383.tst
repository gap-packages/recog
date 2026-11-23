gap> START_TEST("gh-00383.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);

# Issue #383: Bug in RECOG.ForceToOtherField when working over large,
# non-internal fields
# See https://github.com/gap-packages/recog/issues/383
gap> m:=[[Z(17^4)^290]];;
gap> RECOG.ForceToOtherField(m,GF(17,2)) = m;
true

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("gh-00383.tst");
