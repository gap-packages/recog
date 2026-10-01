gap> START_TEST("gh-00038.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);

# See https://github.com/gap-packages/recog/issues/38
gap> RECOG.TestGroup(SymmetricGroup(11), false, Factorial(11));
<recognition node Giant AlmostSimple Size=39916800>

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("gh-00038.tst");
