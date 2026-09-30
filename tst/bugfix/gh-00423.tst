gap> START_TEST("gh-00423.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);

# Issue #423: return of issue #392 with different setup
gap> i := 1226;; Reset(GlobalMersenneTwister, i);; Reset(GlobalRandomSource, i);;
gap> G := Group([ [ 0*Z(3), Z(3)^0 ], [ Z(3), 0*Z(3) ] ]);;
gap> ri := RecognizeGroup(G);;
gap> IsReady(ri);
true

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("gh-00423.tst");
