gap> START_TEST("gh-00393.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);

# Issue #393: projective stabilizer-chain sifting over GF(2) must normalize
# extension-field scalar multiples before calling into genss, otherwise the
# OnPoints optimization hashes the wrong kind of vectors.
# See https://github.com/gap-packages/recog/issues/393
gap> Reset(GlobalMersenneTwister, 1);; Reset(GlobalRandomSource, 1);;
gap> G := SylowSubgroup(GL(6,2),3);;
gap> ri := RecognizeGroup(G);;
gap> IsReady(ri);
true
gap> Size(ri);
81
gap> ForAll(GeneratorsOfGroup(G), x -> SLPforElement(ri, x) <> fail);
true

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("gh-00393.tst");
