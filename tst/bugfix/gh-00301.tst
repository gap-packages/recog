gap> START_TEST("gh-00301.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);

# We had a bug where RECOG.IsScalarMat was used incorrectly (return value was
# assumed to be true or false, but could be an FFE). This example used to
# trigger the error, which looked like this:
#   Error, <expr> must be 'true' or 'false' (not an ffe)
# See https://github.com/gap-packages/recog/pull/301
gap> RECOG.IsThisSL2Natural([ [ [ 0*Z(5), Z(5^2)^9 ], [ Z(5^2)^3, 0*Z(5) ] ], [ [ Z(5), 0*Z(5) ], [ 0*Z(5), Z(5)^3 ] ] ], GF(5^2));
false

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("gh-00301.tst");
