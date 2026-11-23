gap> START_TEST("gh-00519.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);

# The top-level GoProjective kernel recognition can initially sample only a
# proper subgroup of the scalar kernel. Final generator verification must retry
# the kernel after adding the missing residual kernel element.
# See https://github.com/gap-packages/recog/pull/519
gap> seed:=234;; Reset(GlobalMersenneTwister,seed);; Reset(GlobalRandomSource,seed);;
gap> h := GL(19,5);;
gap> g := GroupWithGenerators(ProductReplacer(h)!.team);;
gap> ri := RECOG.TestGroup(g,false,Size(h));;
gap> IsReady(ri);
true
gap> Size(ri) = Size(GL(19,5));
true

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("gh-00519.tst");
