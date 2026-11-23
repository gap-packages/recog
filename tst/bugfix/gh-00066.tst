gap> START_TEST("gh-00066.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);

# Issue #66: direct products over larger fields must not rely on
# CopySubVector only handling IsVectorObj rows.
gap> ri := RecognizeGroup(DirectProduct(SU(3,17), SL(3,17)));;
gap> IsReady(ri);
true

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("gh-00066.tst");
