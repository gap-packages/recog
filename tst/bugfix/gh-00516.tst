gap> START_TEST("gh-00516.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);

# The following test used to run into an error because SLn_godownfromd
# accepted eigenspace dimensions which did not include the expected
# fixed-space dimension.
# See https://github.com/gap-packages/recog/pull/516
gap> seed:=1;;
gap> Reset(GlobalMersenneTwister, seed);;
gap> Reset(GlobalRandomSource, seed);;
gap> h := GL(6,8);;
gap> gens := List([1..10], x -> PseudoRandom(h));;
gap> g := GroupWithGenerators(gens);;
gap> ri := RECOG.TestGroup(g, false, Size(h));;

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("gh-00516.tst");
