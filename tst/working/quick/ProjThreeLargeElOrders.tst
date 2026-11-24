gap> g := Group(Z(5)^0 * [
>    [ [ 0, 1, 0, 0, 0 ],
>      [ 1, 0, 0, 0, 0 ],
>      [ 0, 0, 0, 1, 0 ],
>      [ 0, 0, 1, 0, 0 ],
>      [ 2, 3, 3, 2, 1 ] ],
>    [ [ 0, 0, 1, 0, 0 ],
>      [ 0, 4, 4, 0, 0 ],
>      [ 1, 2, 1, 0, 0 ],
>      [ 0, 0, 0, 0, 1 ],
>      [ 4, 4, 4, 4, 4 ] ],
> ]);;
gap> ri := RECOG.TestGroup(g, true, 660);;

# 2.A8 in degree 8 over GF(5). Its element orders suggest L4(2) = A8, so
# ThreeLargeElOrders tries the black-box recognition of SL(4,2). That cannot
# succeed on a group with a centre and has to give up, so that another method
# takes over.
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);
gap> ResetRandom := function(n)
>   Reset(GlobalMersenneTwister, n);
>   Reset(GlobalRandomSource, n);
> end;;
gap> gens := AtlasGenerators([ "2.A8", [ "2A8G1-f5r8B0.m1",
>                               "2A8G1-f5r8B0.m2" ], 1, 5 ]).generators;;
gap> ForAll([1..20], function(seed)
>   ResetRandom(seed);
>   return SLCR.SLDataStructure(GroupWithMemory(Group(gens)), 2, 1, 4) = fail;
> end);
true
gap> ForAll([1..3], function(seed)
>   local ri;
>   ResetRandom(seed);
>   ri := RecogniseGroup(Group(gens));
>   return IsReady(ri) and Size(ri) = 40320;
> end);
true

# The leaf of the black-box recognition of SL(d,q) stores its size. Else Size
# falls back to GAP's methods for the matrix group, which take long for L3(7)
# in degree 10 over GF(7) and do not give the order of the projective group.
gap> BlackBoxSL := function(G, projective, d, q)
>   local ri;
>   ri := RecogNode(G, projective);
>   repeat
>   until SLCR.FindHom(ri, G, d, q) = Success;
>   return ri;
> end;;
gap> gens := AtlasGenerators([ "L3(7)", [ "L37G1-f7r10aB0.m1",
>                               "L37G1-f7r10aB0.m2" ], 1, 7 ]).generators;;
gap> ri := BlackBoxSL(Group(gens), true, 3, 7);;
gap> HasSize(ri);
true
gap> Size(ri);
1876896
gap> ri := RECOG.TestGroup(Group(gens), false, 1876896);;

# the centre of SL(3,4) has order 3 and consists of scalars
gap> ri := BlackBoxSL(SL(3,4), false, 3, 4);;
gap> HasSize(ri) and Size(ri) = Size(SL(3,4));
true
gap> ri := BlackBoxSL(SL(3,4), true, 3, 4);;
gap> HasSize(ri) and Size(ri) = Size(SL(3,4)) / 3;
true

# In a projective node the SLP of an element must not depend on the scalar:
# the node above finds its kernel, the scalars of the group, as quotients of
# random elements by the evaluated SLPs of their images.
gap> nice := NiceGens(ri);;
gap> ForAll([1..10], function(i)
>   local x;
>   x := PseudoRandom(SL(3,4));
>   return ResultOfStraightLineProgram(SLPforElement(ri, x), nice)
>     = ResultOfStraightLineProgram(SLPforElement(ri, Z(4) * x), nice);
> end);
true

# SL(2,13) on the homogeneous polynomials of degree 7 contains the scalar
# -1. ThreeLargeElOrders takes the group modulo scalars for L2(13).
gap> SymmetricPowerOfSL2 := function(k, q)
>   local power, image;
>   # coefficients of (a x + b y)^n
>   power := {a, b, n} -> List([0..n], i -> Binomial(n, i) * a^(n-i) * b^i);
>   # row i: the image of x^(k-i) y^i under x -> a x + b y, y -> c x + d y
>   image := m -> List([0..k], i -> ProductCoeffs(
>       power(m[1,1], m[1,2], k-i), power(m[2,1], m[2,2], i)));
>   return Group(List(GeneratorsOfGroup(SL(2, q)), image));
> end;;
gap> ForAll([1..5], function(seed)
>   local ri;
>   ResetRandom(seed);
>   ri := RecogniseGroup(SymmetricPowerOfSL2(7, 13));
>   return IsReady(ri) and Size(ri) = 2184;
> end);
true

# SLCR.SLDataStructure gives up if SLCR.SLConstructBasisQ does. No group is
# known on which that happens in dimension 4 or more, so force it.
gap> origConstructBasisQ := SLCR.SLConstructBasisQ;;
gap> SLCR.SLConstructBasisQ := function(bbg, data, Q, Qgamma, d, q)
>   if d = 4 then
>     return fail;
>   fi;
>   return origConstructBasisQ(bbg, data, Q, Qgamma, d, q);
> end;;
gap> ForAll([1..5], function(seed)
>   ResetRandom(seed);
>   return SLCR.SLDataStructure(GroupWithMemory(SL(4,3)), 3, 1, 4) = fail;
> end);
true
gap> SLCR.SLConstructBasisQ := origConstructBasisQ;;
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
