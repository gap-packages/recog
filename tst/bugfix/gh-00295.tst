gap> START_TEST("gh-00295.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);

# Issue #295: the C6 recognizer must reject inconsistent radical block splits
# instead of raising "what's wrong2?" for this reducible alternating-group
# factor.
# See https://github.com/gap-packages/recog/issues/295
gap> Reset(GlobalMersenneTwister, 220);; Reset(GlobalRandomSource, 220);;
gap> deg := 10;;
gap> field := GF(7);;
gap> g := AlternatingGroup(deg);;
gap> gens := List([1..5], x -> PseudoRandom(g));;
gap> mgens := List(gens, x -> PermutationMat(x, deg, field));;
gap> m := GModuleByMats(mgens, field);;
gap> cf := MTX.CompositionFactors(m);;
gap> dims := List(cf, x -> x.dimension);;
gap> max := Maximum(dims);;
gap> pos := Position(dims, max);;
gap> x := PseudoRandom(GL(max, field));;
gap> mgens := List(cf[pos].generators, y -> y^x);;
gap> h := Group(mgens);;
gap> i := 80;; Reset(GlobalMersenneTwister, i);; Reset(GlobalRandomSource, i);;
gap> ri := RecogniseGroup(h);;
gap> IsReady(ri);
true

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("gh-00295.tst");
