gap> START_TEST("gh-00392.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);

# Issue #392: NotAbsolutelyIrred must use immediate verification.
# See https://github.com/gap-packages/recog/issues/392
gap> i := 228;; Reset(GlobalMersenneTwister, i);; Reset(GlobalRandomSource, i);;
gap> G := Group([ [ 0*Z(3), Z(3)^0 ], [ Z(3), 0*Z(3) ] ]);;
gap> ri := RecognizeGroup(G);;
gap> IsReady(ri);
true

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("gh-00392.tst");
