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
gap> ForAll([3, 7, 9, 31], q -> CheckFindStdGens(0, 5, q));
true
gap> ForAll([7, 9, 31], q -> CheckLeaf(0, 5, q));
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
gap> ForAll([2, 3, 4, 9, 31], q -> CheckFindStdGens(1, 6, q));
true
gap> ForAll([3, 4, 5, 8, 31], q -> CheckFindStdGens(-1, 6, q));
true
gap> ForAll([5, 8, 31], q -> CheckLeaf(1, 6, q));
true
gap> ForAll([4, 5, 31], q -> CheckLeaf(-1, 6, q));
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

# Omega^-(4,q) through SL(2,q^2), for every q, also on at most 1000
# points. Its SLPs come from
# RECOG.Omega_RankOneRewrite, which fails outside Omega^-(4,q).
gap> ForAll([2, 3, 4, 9, 31, 32], q -> CheckFindStdGens(-1, 4, q));
true
gap> ForAll([2, 5, 9, 32], q -> CheckLeaf(-1, 4, q));
true
gap> CheckRankOneRewrite := function(e, d, q)
>     local f, type, std, W, G;
>     f := GF(q);
>     type := RECOG.OrthogonalTypes[Position([1, -1, 0], e)];
>     std := RECOG.ClassicalStandardGenerators(type, d, f).all;
>     W := RECOG.Form_RewriteSetup(type, d, f);
>     G := Group(std);
>     return ForAll([1 .. 20], function(i)
>         local x;
>         x := PseudoRandom(G);
>         return ResultOfStraightLineProgram(RECOG.Form_Rewrite(W, x), std)
>                = x;
>     end);
> end;;
gap> ForAll([2, 3, 4, 5, 9, 11, 16], q -> CheckRankOneRewrite(-1, 4, q));
true

# Omega(3,q), q odd, through SL(2,q), as a leaf for q >= 5, also on at
# most 1000 points
gap> ForAll([3, 5, 7, 9, 37, 49], q -> CheckFindStdGens(0, 3, q));
true
gap> ForAll([5, 7, 31, 81], q -> CheckLeaf(0, 3, q));
true
gap> ForAll([3, 5, 9, 37], q -> CheckRankOneRewrite(0, 3, q));
true

# The rewriting fails for matrices outside Omega: diag(gamma, gamma^-1, 1)
# has spinor norm gamma, and a matrix which maps e_1 to w_1 preserves no
# form
gap> ForAll([["O", 3, 37], ["O-", 4, 11]], function(c)
>     local f, W;
>     f := GF(c[3]);
>     W := RECOG.Form_RewriteSetup(c[1], c[2], f);
>     return RECOG.Form_Rewrite(W, RECOG.EmbedBlock(c[2], f, [1, 2],
>                [[Z(c[3]), 0], [0, Z(c[3])^-1]])) = fail
>            and RECOG.Form_Rewrite(W, PermutationMat((1, 3), c[2], f)) = fail;
> end);
true

# Omega(3,3) is soluble and is left to the other methods
gap> ri := RECOG.TestGroup(Omega(3, 3), true, Size(Omega(3, 3)));;
gap> ri!.fhmethsel.successMethod = "ClassicalNatural";
false

# SO(3,37) is Omega(3,37) extended by an element of spinor norm -1
gap> ri := ImageRecogNode(RECOG.TestGroup(SO(3, 37), false, Size(SO(3, 37))));;
gap> [ri!.fhmethsel.successMethod, Size(ImageRecogNode(ri)),
>    KernelRecogNode(ri)!.fhmethsel.successMethod];
[ "ClassicalNatural", 2, "ClassicalNatural" ]

# Omega(7,q), q odd, by the final descent to Omega^+(6,q) and GoingUp; it
# has more than 1000 points for every q
gap> ForAll([3, 5, 9, 31], q -> CheckFindStdGens(0, 7, q));
true
gap> ForAll([3, 13, 31], q -> CheckLeaf(0, 7, q));
true

# Omega^+(4,q) is not quasisimple and no leaf
gap> ri := RECOG.TestGroup(Omega(1, 4, 11), true, Size(Omega(1, 4, 11)) / 2);;
gap> IsLeaf(ri);
false

# GO^-(4,11) has elements of determinant -1, no 4th power in GF(11), and
# SO^-(4,11) is Omega^-(4,11) extended by -1
gap> Reset(GlobalMersenneTwister, 1);;
gap> Reset(GlobalRandomSource, 1);;
gap> G := GO(-1, 4, 11);;
gap> Split(ImageRecogNode(RECOG.TestGroup(G, false, Size(G))));
[ "ProjDeterminant", 2, "ClassicalNatural" ]

# Unsupported input is rejected: degree below 3, Omega^+(4,q), generators
# outside Omega, covers of other types, and a descent from another degree
gap> RECOG.FindStdGens_Omega(Omega(1, 2, 7));
Error, RECOG.FindStdGens_Omega: the degree must be at least 3
gap> RECOG.FindStdGens_Omega(Omega(1, 4, 7));
Error, RECOG.FindStdGens_Omega: Omega^+(4,q) is not supported
gap> RECOG.FindStdGens_Omega(SO(5, 7));
Error, RECOG.FindStdGens_SmallOmega: the generators do not lie in Omega
gap> RECOG.FindStdGens_Omega(SO(3, 37));
Error, RECOG.FindStdGens_RankOneOmega: the generators do not lie in Omega
gap> RECOG.FindStdGens_Omega(GO(-1, 4, 11));
Error, RECOG.FindStdGens_RankOneOmega: the generators do not lie in Omega
gap> RECOG.Omega_SmallDegreeCover("O+", 6, GF(5));
Error, RECOG.Omega_SmallDegreeCover: unsupported group
gap> RECOG.Omega_RankOneCover("O+", 4, GF(5));
Error, RECOG.Omega_RankOneCover: unsupported group
gap> RECOG.Omega_FinalDescent([IdentityMat(6, GF(3))], GF(3), fail, 10);
Error, RECOG.Omega_FinalDescent: <gens> must be 7x7 or 8x8 matrices

# The lift to SL(2,q) resp. SL(2,q^2) fails for matrices which are no
# Kronecker product of the required shape, and the rewriting for -1, which
# does not lie in Omega^-(4,11)
gap> cover := RECOG.Omega_RankOneCover("O", 3, GF(37));;
gap> List([DiagonalMat([Z(37), Z(37)^-1, Z(37)^0]),
>          PermutationMat((1,3), 3, GF(37)), -IdentityMat(3, GF(37))],
>         cover.lift);
[ fail, fail, fail ]
gap> cover := RECOG.Omega_RankOneCover("O-", 4, GF(11));;
gap> List([-IdentityMat(4, GF(11)), PermutationMat((1,2), 4, GF(11))],
>         cover.lift);
[ fail, fail ]
gap> RECOG.Form_Rewrite(RECOG.Form_RewriteSetup("O-", 4, GF(11)),
>                       -IdentityMat(4, GF(11)));
fail

#
gap> SetInfoLevel(InfoOrb, oldInfoOrb);
gap> STOP_TEST("on-small.tst");
