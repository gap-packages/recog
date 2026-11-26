#
gap> START_TEST("sln.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);
gap> oldOrbInfoLevel := InfoLevel(InfoOrb);;
gap> SetInfoLevel(InfoOrb, 0); # genss may warn "Schreier tree is not shallow"
gap> Reset(GlobalMersenneTwister, 1);;
gap> Reset(GlobalRandomSource, 1);;

# RECOG.FindStdGens_SL must express the standard generators of SL(d,q)
# as straight line programs in the given generators, with respect to the
# basis it returns.  q in [2,3,4,5,9] uses the SL4 base case, the other
# cases go through RECOG.RecogniseSL2Natural.
gap> CheckFindStdGens_SL := function(d, p, ext)
>     local q, G, res, gens, std, i;
>     q := p^ext;
>     G := SL(d, q)^PseudoRandom(GL(d, q));
>     res := RECOG.FindStdGens_SL(G);
>     gens := ResultOfStraightLineProgram(res.slpstd, GeneratorsOfGroup(G));
>     std := RECOG.ClassicalStandardGenerators("SL", d, GF(q)).all;
>     for i in [1..Length(std)] do
>         if gens[i]^res.basi <> std[i] then
>             return Concatenation("SL(", String(d), ",", String(q),
>                                  "): generator ", String(i), " is wrong");
>         fi;
>     od;
>     return true;
> end;;
gap> List([[4,3,1], [5,2,1], [4,2,2], [6,3,2], [6,7,1], [7,11,1], [5,2,3], [10,2,1]],
>         args -> CallFuncList(CheckFindStdGens_SL, args));
[ true, true, true, true, true, true, true, true ]

# d = 3 is below the terminal degree of GoingDown, so the final descent
# starts from SL(3,q); q in [2,3,4,5,7] uses a stabiliser chain
gap> ForAll(Concatenation(Filtered([2 .. 32], IsPrimePowerInt),
>                        [101, 2^10, 3^7, 10007]),
>           q -> CheckFindStdGens_SL(3, Factors(q)[1], Length(Factors(q))) = true);
true

# RECOG.SL_Rewrite must return an SLP in the standard generators for
# elements of the standard copy, including those that fix v_1 up to a
# scalar, which need the helper index next
gap> CheckSL_Rewrite := function(d, q)
>     local f, W, std, G, els;
>     f := GF(q);
>     W := RECOG.SL_RewriteSetup(d, f);
>     std := RECOG.ClassicalStandardGenerators("SL", d, f).all;
>     G := Group(std);
>     els := Concatenation(List([1 .. 5], i -> PseudoRandom(G)), std,
>                [One(G), DiagonalMat(Concatenation([Z(q), Z(q)^-1],
>                                                   List([3 .. d], i -> One(f))))]);
>     return ForAll(els,
>                   g -> ResultOfStraightLineProgram(RECOG.SL_Rewrite(W, g), std) = g);
> end;;
gap> ForAll([3 .. 8], d -> ForAll([2, 3, 4, 5, 9], q -> CheckSL_Rewrite(d, q)));
true

# ClassicalNatural makes SL(3,q) with more than 1000 projective points a
# PSLd leaf: for SL(3,q) and GL(3,q) as matrix and as projective groups,
# with scalars on the generators, and with the scalars as a subgroup
gap> Leaf := function(ri)
>     while not IsLeaf(ri) do
>         if ri!.fhmethsel.successMethod = "ProjDeterminant" then
>             ri := KernelRecogNode(ri);
>         else
>             ri := ImageRecogNode(ri);
>         fi;
>     od;
>     return ri!.comment;
> end;;
gap> CheckLeaf_SL3 := function(q)
>     local S, G, c, z, n, scaled, central;
>     S := SL(3, q);
>     G := GL(3, q);
>     c := PseudoRandom(G);
>     z := Z(q);
>     n := Size(S) / Gcd(3, q - 1);
>     scaled := Group(List(GeneratorsOfGroup(S^c),
>                          x -> z^Random(0, q - 2) * x));
>     central := Group(Concatenation(GeneratorsOfGroup(S^c), [z * One(S)]));
>     return Set([Leaf(RECOG.TestGroup(S^c, false, Size(S))),
>                 Leaf(RECOG.TestGroup(G^c, false, Size(G))),
>                 Leaf(RECOG.TestGroup(S^c, true, n)),
>                 Leaf(RECOG.TestGroup(G^c, true, Size(S))),
>                 Leaf(RECOG.TestGroup(scaled, true, n)),
>                 Leaf(RECOG.TestGroup(central, false, n * (q - 1)))]);
> end;;
gap> List([31, 32, 37, 101, 2^10, 3^7, 10007], CheckLeaf_SL3);
[ [ "SL(3,31)_StabilizerChain" ], [ "PSLd" ], [ "PSLd" ], [ "PSLd" ], 
  [ "PSLd" ], [ "PSLd" ], [ "PSLd" ] ]

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> SetInfoLevel(InfoOrb, oldOrbInfoLevel);
gap> STOP_TEST("sln.tst");
