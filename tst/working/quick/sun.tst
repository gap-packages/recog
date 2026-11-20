gap> START_TEST("sun.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);
gap> Reset(GlobalMersenneTwister, 1);;
gap> Reset(GlobalRandomSource, 1);;

# RECOG.FindStdGensSU4 must express the standard generators of SU(4,q) as
# straight line programs in the given generators, with respect to the basis
# it returns, which is a standard basis for a multiple of the form.
gap> CheckFindStdGensSU4 := function(q)
>     local F, G, res, gens, std, form;
>     F := GF(q^2);
>     G := SU(4, q)^PseudoRandom(GL(4, F));
>     res := RECOG.FindStdGensSU4(GeneratorsOfGroup(G), F);
>     gens := ResultOfStraightLineProgram(res.slp, GeneratorsOfGroup(G));
>     std := RECOG.ClassicalStandardGenerators("SU", 4, F).all;
>     form := RECOG.ClassicalInvariantForm("SU", GeneratorsOfGroup(G), F);
>     form := RECOG.FormGram(form, res.bas);
>     return List(gens, g -> res.bas * g * res.bas^-1) = std
>            and form = form[1, 2] * RECOG.ClassicalStandardForm("SU", 4, F);
> end;;
gap> Filtered([3, 5, 7, 9, 11, 13, 25, 27, 49, 81, 121, 243],
>             q -> not CheckFindStdGensSU4(q));
[  ]

# The same for RECOG.FindStdGens_SU and SU(d,q).
gap> CheckFindStdGens_SU := function(d, q)
>     local F, G, res, gens, std, i;
>     F := GF(q^2);
>     G := SU(d, q)^PseudoRandom(GL(d, F));
>     res := RECOG.FindStdGens_SU(G);
>     gens := ResultOfStraightLineProgram(res.slpstd, GeneratorsOfGroup(G));
>     std := RECOG.ClassicalStandardGenerators("SU", d, F).all;
>     for i in [1..Length(std)] do
>         if gens[i]^res.basi <> std[i] then
>             return Concatenation("SU(", String(d), ",", String(q),
>                                  "): generator ", String(i), " is wrong");
>         fi;
>     od;
>     return true;
> end;;
gap> List([[6,3], [8,3], [12,3], [6,5], [8,7], [6,9], [6,13], [10,11],
>          [6,25], [6,27], [24,3], [4,5]],
>         args -> CallFuncList(CheckFindStdGens_SU, args));
[ true, true, true, true, true, true, true, true, true, true, true, true ]

# RECOG.Form_Rewrite must return an SLP in the standard generators for
# elements of the standard copy
gap> CheckForm_Rewrite := function(d, q)
>     local f, W, std, G, els;
>     f := GF(q^2);
>     W := RECOG.Form_RewriteSetup("SU", d, f);
>     std := RECOG.ClassicalStandardGenerators("SU", d, f);
>     G := Group(std.all);
>     els := Concatenation(List([1 .. 4], i -> PseudoRandom(G)), std.all,
>                          [One(G), std.delta^std.u, std.y^std.v]);
>     return ForAll(els, g -> ResultOfStraightLineProgram(
>                                 RECOG.Form_Rewrite(W, g), std.all) = g);
> end;;
gap> ForAll([4, 6, 8], d -> ForAll([3, 5, 9], q -> CheckForm_Rewrite(d, q)));
true

# ClassicalNatural makes natural SU(d,q) a PSU leaf, also with scalars of
# GU(d,q) on the generators, and its SLPs accept any scalar. Generators
# with other scalars are left out: with them, RecogniseClassical often
# misses the form, as ClassicalForms_ScalarMultipleFrobenius of Forms
# 1.3.0 returns a wrong scalar. GU(4,5) is no leaf: scalars cannot bring
# its determinants of order 6 to 1, so it maps onto C2 above a PSU leaf.
gap> Leaf := function(ri)
>     if not IsLeaf(ri) then
>         ri := ImageRecogNode(ri);
>     fi;
>     return ri;
> end;;
gap> IsScalarMultiple := function(x, y)
>     local pos;
>     pos := PositionNonZero(y[1]);
>     return x = x[1, pos] / y[1, pos] * y;
> end;;
gap> S := SU(6, 3)^PseudoRandom(GL(6, 9));;
gap> ri := Leaf(RECOG.TestGroup(S, false, Size(S)));;
gap> ri!.fhmethsel.successMethod;
"ClassicalNatural"
gap> ForAll([1 .. 5], function(i)
>     local x;
>     x := PseudoRandom(S);
>     return IsScalarMultiple(ResultOfStraightLineProgram(
>                SLPforElement(ri, Z(9)^i * x), NiceGens(ri)), x);
> end);
true
gap> G := Group(List(GeneratorsOfGroup(SU(4, 5)), x -> Z(25)^(4 * Random([0 .. 5])) * x));;
gap> Leaf(RECOG.TestGroup(G, true, Size(SU(4, 5)) / 2))!.fhmethsel.successMethod;
"ClassicalNatural"
gap> Leaf(RECOG.TestGroup(GU(4, 5), false, Size(GU(4, 5))))!.fhmethsel.successMethod;
"ClassicalNatural"

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("sun.tst");
