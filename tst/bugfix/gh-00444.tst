gap> START_TEST("gh-00444.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);

# Issue #444: a projective C6 block kernel must keep the full scalar-block
# size when passing through DoBaseChangeForBlocks and BlocksBackToMats.
# See https://github.com/gap-packages/recog/issues/444
gap> i := 1;; Reset(GlobalMersenneTwister, i);; Reset(GlobalRandomSource, i);;
gap> m := ClassicalMaximals("L",8,7);;
gap> g := m[10];;
gap> re := RECOG.New2RecogniseC6(g);;
gap> hom := GroupHomByFuncWithData(g, GroupWithGenerators(re.igens),
>   RECOG.HomFuncActionOnBlocks,
>   rec(r := re.r, n := re.n, q := re.q, blks := re.basis.blocks));;
gap> k := KernelOfMultiplicativeGeneralMapping(hom);;
gap> data := rec(hints := []);;
gap> data.t := re.basis.blocks.blocks;;
gap> data.blocksize := 8 / re.basis.blocks.ell;;
gap> AddMethod(data.hints, FindHomMethodsProjective.DoBaseChangeForBlocks, 2000);;
gap> ri := RecogniseGeneric(k, FindHomDbProjective, "", data);;
gap> IsReady(ri);
true
gap> h := Group(List(GeneratorsOfGroup(k), RECOG.HomBackToMats));;
gap> Size(h);
139968
gap> Size(ri);
139968

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("gh-00444.tst");
