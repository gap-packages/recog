gap> START_TEST("gh-00417.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);

# Issue #417: a contradictory homogeneous C3/C5 witness for SO(+1,4,3)
# must not raise an internal error.
# See https://github.com/gap-packages/recog/issues/417
gap> i := 138;; Reset(GlobalMersenneTwister, 1);; Reset(GlobalRandomSource, i);;
gap> ri := RecognizeGroup(SO(+1,4,3));;
gap> IsReady(ri);
true

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("gh-00417.tst");
