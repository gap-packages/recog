gap> START_TEST("gh-00399.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);

# Issue #399: The semilinear rewrite for NotAbsolutelyIrred must accept
# genuine semilinear elements, not only E-linear ones. This random seed used
# to produce a failed recognition node on the branch for issue #399.
gap> i:=4;; Reset(GlobalRandomSource,i);; Reset(GlobalMersenneTwister,1);;
gap> ri:=RecognizeGroup(SO(+1,4,3));;
gap> IsReady(ri);
true

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("gh-00399.tst");
