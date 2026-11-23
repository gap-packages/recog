gap> START_TEST("gh-00503.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);

# Issue #503: the C3/C5 semilinear branch must seed generators with trivial
# field-automorphism action into the kernel, otherwise kernel recognition can
# settle on a proper subgroup and fail final verification.
# See https://github.com/gap-packages/recog/issues/503
gap> x1 := [ [ Z(11)^7, Z(11)^0 ], [ Z(11)^8, Z(11)^5 ] ];;
gap> x2 := [ [ Z(11)^5, 0*Z(11) ], [ 0*Z(11), Z(11)^5 ] ];;
gap> x3 := [ [ Z(11)^4, Z(11) ], [ Z(11)^6, Z(11)^9 ] ];;
gap> G := Group([x1, x2, x3]);;
gap> i := 35;; Reset(GlobalRandomSource, i);; Reset(GlobalMersenneTwister, i);;
gap> ri := RecognizeGroup(G);;
gap> IsReady(ri);
true
gap> Size(ri);
24
gap> IsCorrect(ri);
true

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("gh-00503.tst");
