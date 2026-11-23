gap> START_TEST("gh-00510.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);

# Issue #510: SnAnUnknownDegree must not spend a long time on this
# non-projective matrix group with a hidden nontrivial scalar.
# See https://github.com/gap-packages/recog/issues/510
gap> gens := Z(3)^0 * [
> [ [ 1, 0, 0, 0, 0, 0 ],
> [ 1, 1, 1, 1, 1, 0 ],
> [ 0, 0, 1, 0, 0, 0 ],
> [ 2, 0, 0, 1, 2, 0 ],
> [ 0, 0, 0, 0, 1, 0 ],
> [ 1, 0, 1, 1, 1, 1 ] ],
> [ [ 1, 2, 2, 1, 0, 2 ],
> [ 0, 1, 0, 0, 0, 0 ],
> [ 2, 0, 0, 2, 0, 2 ],
> [ 1, 0, 2, 0, 0, 2 ],
> [ 0, 1, 2, 0, 1, 2 ],
> [ 1, 1, 1, 1, 0, 1 ] ],
> [ [ 2, 0, 0, 0, 0, 0 ],
> [ 0, 2, 0, 0, 0, 0 ],
> [ 0, 0, 2, 0, 0, 0 ],
> [ 0, 0, 0, 2, 0, 0 ],
> [ 0, 0, 0, 0, 2, 0 ],
> [ 0, 0, 0, 0, 0, 2 ] ]
> ];;
gap> G := Group([gens[3] * gens[1], gens[1], gens[2]]);;
gap> ForAny(GeneratorsOfGroup(G), RECOG.IsScalarMat);
false
gap> i := 1;; Reset(GlobalRandomSource, i);; Reset(GlobalMersenneTwister, i);;
gap> FindHomMethodsGeneric.SnAnUnknownDegree(RecogNode(G));
"NeverApplicable"

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("gh-00510.tst");
