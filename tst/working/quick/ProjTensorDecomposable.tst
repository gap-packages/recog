gap> START_TEST("ProjTensorDecomposable.tst");
gap> ReadPackage("recog","tst/products.g");;
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);

# C3C5 and D247 usually find a tensor decomposition first, so call the method
# directly. Depending on the normal subgroup it samples, it succeeds or gives
# up for the moment.
gap> TryTensorDecomposable := function(G, seed)
>   Reset(GlobalMersenneTwister, seed);
>   Reset(GlobalRandomSource, seed);
>   return CallRecogMethod(FindHomMethodsProjective.TensorDecomposable,
>                          RecogNode(Group(GeneratorsOfGroup(G)), true));
> end;;

# a tensor product: the restriction to the normal subgroup is homogeneous
gap> G := TensorProductOfMatrixGroup(GL(2,5), GL(3,5));;
gap> res := List([1..10], seed -> TryTensorDecomposable(G, seed));;
gap> ForAll(res, x -> x in [Success, TemporaryFailure]);
true
gap> Success in res;
true

# (GL(1,16) wr Sym(4)) meet SL(4,16): the diagonal subgroup has four
# homogeneous components, and the method acts on them
gap> z := Z(16);;
gap> G := Group(DiagonalMat([z, z^-1, z^0, z^0]),
>               PermutationMat((1,2), 4, GF(16)),
>               PermutationMat((1,2,3,4), 4, GF(16)));;
gap> res := List([1..10], seed -> TryTensorDecomposable(G, seed));;
gap> ForAll(res, x -> x in [Success, TemporaryFailure]);
true
gap> Success in res;
true
gap> ri := RECOG.TestGroup(G, true, 15^3 * 24);;

# a subgroup that is not normal: the group does not permute its homogeneous
# components
gap> RECOG.FindTensorDecomposition(GL(2,5),
>                                  Group(DiagonalMat([Z(5), Z(5)^0])));
fail

# SL(2,3) tensor 1 is homogeneous, but SL(4,3) does not normalise it and
# respects no tensor decomposition. The method finds its subgroup by a random
# search, so hand it this one.
gap> G := SL(4,3);;
gap> N := Group(List(GeneratorsOfGroup(SL(2,3)),
>                    x -> KroneckerProduct(x, IdentityMat(2, GF(3)))));;
gap> RECOG.FindTensorDecomposition(G, N).blocksize;
2
gap> origFindTensorKernel := RECOG.FindTensorKernel;;
gap> RECOG.FindTensorKernel := {G, onlyone} -> N;;
gap> CallRecogMethod(FindHomMethodsProjective.TensorDecomposable,
>                    RecogNode(G, true)) = TemporaryFailure;
true
gap> RECOG.FindTensorKernel := origFindTensorKernel;;

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("ProjTensorDecomposable.tst");
