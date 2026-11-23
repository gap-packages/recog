gap> START_TEST("gh-00313.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);

# Issue #313: an unsatisfied determinant congruence in SLConstructive must
# cause recognition to back out, not raise a ModRat error.
# See https://github.com/gap-packages/recog/issues/313
gap> i := 58;; Reset(GlobalMersenneTwister, i);; Reset(GlobalRandomSource, i);;
gap> ri := RecognizeGroup(ClassicalMaximals("L",4,3)[8]);;
gap> IsReady(ri);
true

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("gh-00313.tst");
