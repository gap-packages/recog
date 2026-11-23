gap> START_TEST("gh-00033.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);

# Issue #33: Generic projective image verification must also accept
# representatives that differ by scalars after rewriting over a bigger field.
# See https://github.com/gap-packages/recog/issues/33
gap> i := 123;; Reset(GlobalMersenneTwister, i);; Reset(GlobalRandomSource, i);;
gap> ri := RecognizeGroup(ClassicalMaximals("L",4,3)[7]);;
gap> IsReady(ri);
true

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("gh-00033.tst");
