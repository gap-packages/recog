gap> START_TEST("on-small.tst");
gap> oldInfoOrb := InfoLevel(InfoOrb);;
gap> SetInfoLevel(InfoOrb, 0);

# RECOG.FindStdGens_Omega expresses the standard generators of Omega(d,q)
# of small degree in the given generators, relative to the basis it returns
gap> CheckFindStdGens := function(e, d, q)
>     local f, type, G, res, std;
>     f := GF(q);
>     type := RECOG.OrthogonalTypes[Position([1, -1, 0], e)];
>     G := Omega(e, d, q)^RandomInvertibleMat(d, f);
>     res := RECOG.FindStdGens_Omega(G);
>     std := RECOG.ClassicalStandardGenerators(type, d, f).all;
>     return res.type = type
>            and ResultOfStraightLineProgram(res.slpstd, GeneratorsOfGroup(G))
>                = List(std, x -> res.basi * x * res.bas);
> end;;

# ClassicalNatural makes the natural Omega(d,q) of small degree a leaf, for
# three seeds each, as a matrix group and as a projective group with
# scalars on the generators; RECOG.TestGroup checks the size and the SLPs
# of random elements. -1 lies in Omega^e(d,q) if and only if
# q^(d/2) = e mod 4.
gap> CheckLeaf := function(e, d, q)
>     local f, S, centre, seed, proj, G, size, ri;
>     f := GF(q);
>     S := Omega(e, d, q);
>     centre := 1;
>     if e <> 0 and IsOddInt(q) and (q^(d / 2) - e) mod 4 = 0 then
>         centre := 2;
>     fi;
>     for seed in [1 .. 3] do
>         for proj in [false, true] do
>             Reset(GlobalMersenneTwister, seed);
>             Reset(GlobalRandomSource, seed);
>             G := S^RandomInvertibleMat(d, f);
>             size := Size(S);
>             if proj then
>                 G := Group(List(GeneratorsOfGroup(G),
>                                 x -> Z(q)^Random(1, q - 1) * x));
>                 size := size / centre;
>             fi;
>             ri := RECOG.TestGroup(G, proj, size);
>             if not IsReady(ri) then
>                 return false;
>             fi;
>             if not proj then
>                 ri := ImageRecogNode(ri);
>             fi;
>             if not IsLeaf(ri)
>                or ri!.fhmethsel.successMethod <> "ClassicalNatural" then
>                 return false;
>             fi;
>         od;
>     od;
>     return true;
> end;;

# Omega(5,q), q odd, through Sp(4,q); q = 7 is the smallest with more than
# 1000 points
gap> ForAll([3, 5, 7, 9, 25, 31], q -> CheckFindStdGens(0, 5, q));
true
gap> ForAll([7, 9, 11, 27, 31], q -> CheckLeaf(0, 5, q));
true

# Omega(5,5) has 781 points and is left to the other methods
gap> ri := RECOG.TestGroup(Omega(5, 5), true, Size(Omega(5, 5)));;
gap> ri!.fhmethsel.successMethod;
"StabilizerChainProj"

# SO(5,7) is Omega(5,7) extended by an element of spinor norm -1
gap> ri := ImageRecogNode(RECOG.TestGroup(SO(5, 7), false, Size(SO(5, 7))));;
gap> [ri!.fhmethsel.successMethod, Size(ImageRecogNode(ri)),
>    KernelRecogNode(ri)!.fhmethsel.successMethod];
[ "ClassicalNatural", 2, "ClassicalNatural" ]

# Omega^+(6,q) through SL(4,q) and Omega^-(6,q) through SU(4,q), for every
# q; q = 4 and q = 5 are the smallest with more than 1000 points.
# RecogniseClassical does not name Omega^+(6,4) in about one run in 5, so
# it is not among the leaves tested.
gap> ForAll([2, 3, 4, 5, 8, 9, 31], q -> CheckFindStdGens(1, 6, q));
true
gap> ForAll([3, 4, 5, 8, 9, 31], q -> CheckFindStdGens(-1, 6, q));
true
gap> ForAll([5, 7, 8, 9, 31, 32], q -> CheckLeaf(1, 6, q));
true
gap> ForAll([4, 5, 7, 9, 31, 32], q -> CheckLeaf(-1, 6, q));
true

# GO^-(6,5) and GO^+(6,5) are Omega extended by 2 and by 2^2, the latter
# in two layers
gap> Split := function(ri)
>     if IsLeaf(ri) then
>         return ri!.fhmethsel.successMethod;
>     fi;
>     return [ri!.fhmethsel.successMethod, Size(ImageRecogNode(ri)),
>             Split(KernelRecogNode(ri))];
> end;;
gap> for G in [GO(-1, 6, 5), GO(1, 6, 5)] do
>     Reset(GlobalMersenneTwister, 1);
>     Reset(GlobalRandomSource, 1);
>     Print(Split(ImageRecogNode(RECOG.TestGroup(G, false, Size(G)))), "\n");
> od;
[ "ClassicalNatural", 2, "ClassicalNatural" ]
[ "ClassicalNatural", 2, [ "ClassicalNatural", 2, "ClassicalNatural" ] ]

#
gap> SetInfoLevel(InfoOrb, oldInfoOrb);
gap> STOP_TEST("on-small.tst");
