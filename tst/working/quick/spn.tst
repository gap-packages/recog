gap> START_TEST("spn.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);
gap> Reset(GlobalMersenneTwister, 1);;
gap> Reset(GlobalRandomSource, 1);;

# RECOG.FindStdGens_Sp must express the standard generators of Sp(d,q)
# of RECOG.ClassicalStandardGenerators as straight line programs in the
# given generators, with respect to the basis it returns.
gap> CheckFindStdGens_Sp := function(d, p, ext)
>     local q, G, res, gens, std, i;
>     q := p^ext;
>     G := Sp(d, q)^PseudoRandom(GL(d, q));
>     res := RECOG.FindStdGens_Sp(G);
>     gens := ResultOfStraightLineProgram(res.slpstd, GeneratorsOfGroup(G));
>     std := RECOG.ClassicalStandardGenerators("Sp", d, GF(q)).all;
>     for i in [1..Length(std)] do
>         if gens[i]^res.basi <> std[i] then
>             return Concatenation("Sp(", String(d), ",", String(q),
>                                  "): generator ", String(i), " is wrong");
>         fi;
>     od;
>     return true;
> end;;
gap> List([[4,3,1], [4,5,1], [6,3,1], [6,7,1], [6,3,2], [8,3,1], [12,3,1],
>          [8,5,1], [10,7,1], [14,3,2], [12,11,1]],
>         args -> CallFuncList(CheckFindStdGens_Sp, args));
[ true, true, true, true, true, true, true, true, true, true, true ]

# RECOG.Form_Rewrite must return an SLP in the standard generators for
# elements of the standard copy
gap> CheckForm_Rewrite := function(d, q)
>     local f, W, std, G, els;
>     f := GF(q);
>     W := RECOG.Form_RewriteSetup("Sp", d, f);
>     std := RECOG.ClassicalStandardGenerators("Sp", d, f);
>     G := Group(std.all);
>     els := Concatenation(List([1 .. 4], i -> PseudoRandom(G)), std.all,
>                          [One(G), std.s^std.v]);
>     return ForAll(els, g -> ResultOfStraightLineProgram(
>                                 RECOG.Form_Rewrite(W, g), std.all) = g);
> end;;
gap> ForAll([4, 6, 8, 10], d -> ForAll([3, 5, 9, 25], q -> CheckForm_Rewrite(d, q)));
true

# ClassicalNatural makes natural Sp(d,q) a PSp leaf, also with scalars on
# the generators, but not a conformal symplectic group
gap> Leaf := function(ri)
>     if not IsLeaf(ri) then
>         ri := ImageRecogNode(ri);
>     fi;
>     return ri!.fhmethsel.successMethod;
> end;;
gap> S := Sp(8, 3);;
gap> Leaf(RECOG.TestGroup(S^PseudoRandom(GL(8, 3)), false, Size(S)));
"ClassicalNatural"
gap> G := Group(List(GeneratorsOfGroup(Sp(6, 5)), x -> Z(5)^Random([0 .. 3]) * x));;
gap> Leaf(RECOG.TestGroup(G, true, Size(Sp(6, 5)) / 2));
"ClassicalNatural"
gap> F := InvariantBilinearForm(S).matrix;;
gap> simil := First(List(Tuples([1, -1] * Z(3)^0, 8), DiagonalMat),
>                   x -> x * F * TransposedMat(x) = -F);;
gap> Leaf(RECOG.TestGroup(Group(Concatenation(GeneratorsOfGroup(S), [simil])),
>                         false, 2 * Size(S)));
"StabilizerChainProj"

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("spn.tst");
