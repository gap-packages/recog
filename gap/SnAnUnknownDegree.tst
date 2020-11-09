#@local testFunction, IsBolsteringElement, degrees
#@local altGroups, symGroups, permMatGroup, altMatGroups, nonAltOrSymGroups
#@local ri, g, c, r, i, x, slp
#@local sets, S11On2Sets, res, isoData, gens, g1, img1, g2, img2
#
# testing matrix:
# - isomorphic: yes, no
# different representations:
# - permutation groups: natural, on 2-subsets
# - finitely presented group
# - permutation matrices: compressed matrices, uncompressed matrices
# - projective matrix groups
#
# TODO: Use RECOG.TestGroup?
# TODO: better name for testFunction
# tests ThreeCycleCandidatesIterator and BolsteringElements
gap> testFunction := function(G, eps, N)
>     local ri, iterator, candidate, i, j;
>     ri := EmptyRecognitionInfoRecord(rec(), G, false);
>     iterator := ThreeCycleCandidatesIterator(ri, eps, N);
>     for i in [1 .. 10] do
>         candidate := iterator();
>         for j in [1 .. 10] do
>             if candidate <> NeverApplicable
>                     and candidate <> TemporaryFailure then
>                 BolsteringElements(ri, candidate, eps,
>                                    N);
>             fi;
>         od;
>     od;
> end;;

#
# x : permutation
# c : permutation,
#     should be a 3-cycle
#
# Returns true, if x is a bolstering element with respect to the 3-cycle c.
#
# Let c = (u, v, w). We call x a bolstering element with respect to c, if
# x = (v, a_1, ..., a_alpha)(w, b_1, ..., b_beta)(...) or
# x = (v, a_1, ..., a_alpha, w, b_1, ..., b_beta)(...)
# with u in fix(x) and alpha, beta >= 2.
gap> IsBolsteringElement :=
> function(x, c)
>     local suppC, dist, i, k, p, pos1;
>     # suppC = [u, v, w]
>     suppC := MovedPoints(c);
>     if Size(suppC) <> 3 then return false; fi;
>     # dist = [k_u, k_v, k_w],
>     # where for each p in suppC, k_p is the minimal integer such that p^(x^k) in suppC
>     dist := [0, 0, 0];
>     for i in [1..3] do
>         k := 1;
>         p := suppC[i]^x;
>         while not p in suppC do
>             k := k + 1;
>             p := p ^ x;
>         od;
>         dist[i] := k;
>     od;
>     # One point of suppC is fixed by x
>     pos1 := PositionProperty(dist, k -> k = 1);
>     if pos1 = fail then return false; fi;
>     Remove(dist, pos1);
>     # The other two points of cuppC have distance at least 2
>     if ForAny(dist, k -> k < 2) then return false; fi;
>     return true;
> end;;
gap> degrees := Concatenation(
>     [10, 12, 20, 21, 30, 35, 40, 42, 50, 51],
>     Primes{[5 .. 15]}
> );;
gap> degrees := degrees{[1, 2, 11, 12]};;

# TODO: more non-isomorphic examples
# TODO: add projective groups
gap> altGroups := List(degrees, AlternatingGroup);;
gap> symGroups := List(degrees, SymmetricGroup);;
gap> permMatGroup := G -> Group(List(
>     GeneratorsOfGroup(G),
>     x -> ImmutableMatrix(7, PermutationMat(x, NrMovedPoints(G), GF(7)))
> ));;
gap> altMatGroups := List([10],
>                          n -> permMatGroup(AlternatingGroup(n)));;
gap> nonAltOrSymGroups := [
>     DihedralGroup(IsPermGroup, 10),
>     #DihedralGroup(IsPcGroup, 10),
>     #DihedralGroup(IsPermGroup, 2000),
>     #DihedralGroup(IsPcGroup, 2000),
>     #PSL(3, 5),
>     SL(3, 5),
>     #permMatGroup(DihedralGroup(IsPermGroup, 10)),
>     #Omega(-1, 4, 5),
>     #Omega(+1, 4, 5),
>     #Omega(0, 5, 5),
> ];;

# FIXME: This is super slow.
# ThreeCycleCandidates
gap> for i in [1 .. Length(degrees)] do
>     testFunction(altGroups[i], 1/100, degrees[i]);
>     testFunction(symGroups[i], 1/100, degrees[i]);
> od;
gap> for i in [1 .. Length(altMatGroups)] do
>     testFunction(altMatGroups[i], 1/100, 13);
> od;
gap> for i in [1 .. Length(nonAltOrSymGroups)] do
>     testFunction(nonAltOrSymGroups[i], 1/100, 15);
> od;

# IsFixedPoint
gap> ri := EmptyRecognitionInfoRecord(rec(), SymmetricGroup(10), false);;
gap> g := (1,2,3,4,5,6,7,8);;
gap> c := (1,2,3);;
gap> r := (1,2)(4,5,6);;
gap> IsFixedPoint(ri, g,c,r);
true
gap> r := (2,3,4);;
gap> IsFixedPoint(ri, g,c,r);
false

# AdjustCycle
gap> ri := EmptyRecognitionInfoRecord(rec(), SymmetricGroup(10), false);;
gap> g := (1,2,3,4,5,6,7,8);;
gap> c := (1,2,3);;
gap> r := (4,5);;
gap> AdjustCycle(ri, g, c, r, 8);
(3,5)
gap> r := (3,4,5);;
gap> AdjustCycle(ri, g, c, r, 8);
(3,4,5)
gap> r := (2,5);;
gap> AdjustCycle(ri, g, c, r, 8);
(3,5)
gap> r := (2,4,5);;
gap> AdjustCycle(ri, g, c, r, 8);
(3,5,4)
gap> r := (2,3,5);;
gap> AdjustCycle(ri, g, c, r, 8);
(3,4,5)
gap> r := (1,5);;
gap> AdjustCycle(ri, g, c, r, 8);
(3,5)
gap> r := (1,4,5);;
gap> AdjustCycle(ri, g, c, r, 8);
(3,5,4)
gap> r := (1,3,4,5);;
gap> AdjustCycle(ri, g, c, r, 8);
(3,6,4,5)
gap> r := (1,2,5);;
gap> AdjustCycle(ri, g, c, r, 8);
(3,5,4)
gap> r := (1,2,3,5);;
gap> AdjustCycle(ri, g, c, r, 8);
(3,5,4,6)

# BuildCycle
gap> ri := EmptyRecognitionInfoRecord(rec(), SymmetricGroup(10), false);;

# c = (u,v,w)
gap> c := (1,2,3);;

# Form 1: x = (v,a_1,...,a_alpha) * (w,b_1,....,b_beta) * (...)
# alpha - beta = 0
gap> x := (2,4,5,6)* (3,7,8,9);;
gap> BuildCycle(ri, c, x, 10);
[ (1,2,3,4,7,5,8,6,9), 9 ]

# alpha - beta = -1
gap> x := (2,4,5,6)* (3,7,8,9,10);;
gap> BuildCycle(ri, c, x, 10);
[ (1,2,3,4,7,5,8,6,9), 9 ]

# alpha - beta = 1
gap> x := (2,4,5,6,10)* (3,7,8,9);;
gap> BuildCycle(ri, c, x, 10);
[ (1,2,3,4,7,5,8,6,9), 9 ]

# alpha - beta = -2
gap> x := (2,4,5) * (3,7,8,9,10);;
gap> BuildCycle(ri, c, x, 10);
[ (1,2,3,4,7,5,8,10,9), 9 ]

# alpha - beta = 2
gap> x := (2,4,5,6,10) * (3,7,8);;
gap> BuildCycle(ri, c, x, 10);
[ (1,2,3,4,7,5,8,6,10), 9 ]

# Form 2: x = (v,a_1,...,a_alpha,w,b_1,....,b_beta) * (...)
# alpha - beta = 0
gap> x := (2,4,5,6,3,7,8,9);;
gap> BuildCycle(ri, c, x, 10);
[ (1,2,3,4,7,5,8,6,9), 9 ]

# alpha - beta = -1
gap> x := (2,4,5,6,3,7,8,9,10);;
gap> BuildCycle(ri, c, x, 10);
[ (1,2,3,4,7,5,8,6,9), 9 ]

# alpha - beta = 1
gap> x := (2,4,5,6,10,3,7,8,9);;
gap> BuildCycle(ri, c, x, 10);
[ (1,2,3,4,7,5,8,6,9), 9 ]

# alpha - beta = -2
gap> x := (2,4,5,3,7,8,9,10);;
gap> BuildCycle(ri, c, x, 10);
[ (1,2,3,4,7,5,8,10,9), 9 ]

# alpha - beta = 2
gap> x := (2,4,5,6,10,3,7,8);;
gap> BuildCycle(ri, c, x, 10);
[ (1,2,3,4,7,5,8,6,10), 9 ]

# Construct isomorphism between S_11 on 2-sets and S_11 in natural
# representation.
gap> sets := Combinations([1 .. 11], 2);;
gap> S11On2Sets := Action(SymmetricGroup(11), sets, OnSets);;
gap> ri := EmptyRecognitionInfoRecord(rec(), S11On2Sets, false);;
gap> FindHomMethodsGeneric.SnAnUnknownDegree(ri);;
gap> isoData := ri!.SnAnUnknownDegreeIsoData;;
gap> gens := GeneratorsOfGroup(S11On2Sets);;
gap> g1 := gens[1];;
gap> img1 := FindImageSn(ri, 11, g1, isoData[2][1], isoData[2][2],
>                        isoData[3][1], isoData[3][2]);;
gap> CycleStructurePerm(img1);
[ ,,,,,,,,, 1 ]
gap> g2 := gens[2];;
gap> img2 := FindImageSn(ri, 11, g2, isoData[2][1], isoData[2][2],
>                        isoData[3][1], isoData[3][2]);;
gap> CycleStructurePerm(img2);
[ 1 ]

# FindHomMethodsGeneric.SnAnUnknownDegree
gap> sets := Combinations([1 .. 11], 2);;
gap> S11On2Sets := Action(SymmetricGroup(11), sets, OnSets);;
gap> ri := EmptyRecognitionInfoRecord(rec(), S11On2Sets, false);;
gap> FindHomMethodsGeneric.SnAnUnknownDegree(ri);
true
gap> Size(ri);
39916800
gap> Size(SymmetricGroup(11));
39916800

# Check Slp function
gap> ri := EmptyRecognitionInfoRecord(rec(), SymmetricGroup(11), false);;
gap> FindHomMethodsGeneric.SnAnUnknownDegree(ri);
true
gap> x := PseudoRandom(Grp(ri));;
gap> slp := SLPforElement(ri, x);;
gap> x = ResultOfStraightLineProgram(slp, NiceGens(ri));
true
