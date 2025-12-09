#@local testFunction, IsBolsteringElement, data
#@local altGroups, symGroups, permMatGroup, altMatGroups, nonAltOrSymGroups
#@local ri, g, c, r, i, x, slp
#@local S11On2Sets, d, sets, SdOn2Sets, success, res, isoData, gens, g1, img1, g2, img2
#@local SymOnKSets, AltOnKSets
#@local db
#
# HACK to insert the method
gap> AddMethod(FindHomDbPerm, FindHomMethodsGeneric.SnAnUnknownDegree, 58);;
gap> AddMethod(FindHomDbMatrix, FindHomMethodsGeneric.SnAnUnknownDegree, 1070);;
gap> AddMethod(FindHomDbProjective, FindHomMethodsGeneric.SnAnUnknownDegree, 1220);;

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
# tests RECOG.ThreeCycleCandidatesIterator and RECOG.BolsteringElements
gap> testFunction := function(G, eps, N)
>     local ri, iterator, candidate, i, j;
>     ri := RecogNode(G);
>     iterator := RECOG.ThreeCycleCandidatesIterator(ri, RECOG.ThreeCycleCandidatesConstants(eps, N));
>     for i in [1 .. 4] do
>         candidate := iterator();
>         for j in [1 .. 4] do
>             if candidate <> NeverApplicable
>                     and candidate <> TemporaryFailure then
>                 RECOG.BolsteringElements(ri, candidate, eps,
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

# For each entry (d, k) we construct Sym(d)/Alt(d) acting on k-sets.
# For each entry (d, k), we must have 2 * k ^ 2 > d,
# otherwise LargeBasePrimitive recognises the group instead of SnAnUnknownDegree.
gap> data := [[11, 3], [12, 3], [13, 3]];;

# TODO: more non-isomorphic examples
# TODO: add projective groups
#
# SymmetricGroup action on k-sets
gap> SymOnKSets := function(d, k)
>     local sets;
>     sets := Combinations([1 .. d], k);;
>     return Action(SymmetricGroup(d), sets, OnSets);;
> end;;

#
# AlternatingGroup action on 2-sets
gap> AltOnKSets := function(d, k)
>     local sets;
>     sets := Combinations([1 .. d], k);;
>     return Action(AlternatingGroup(d), sets, OnSets);;
> end;;

#
gap> altGroups := List(data, entry -> AltOnKSets(entry[1], entry[2]));;
gap> symGroups := List(data, entry -> SymOnKSets(entry[1], entry[2]));;
gap> permMatGroup := G -> Group(List(
>     GeneratorsOfGroup(G),
>     x -> ImmutableMatrix(7, PermutationMat(x, NrMovedPoints(G), GF(7)))
> ));;
gap> altMatGroups := List([11],
>                          n -> permMatGroup(AlternatingGroup(n)));;
gap> nonAltOrSymGroups := [
>     DihedralGroup(IsPermGroup, 10),
>     #DihedralGroup(IsPcGroup, 10),
>     #DihedralGroup(IsPermGroup, 2000),
>     #DihedralGroup(IsPcGroup, 2000),
>     PSL(3, 5),
>     SL(3, 5),
>     Omega(-1, 4, 5),
>     Omega(-1, 4, 3),
>     Omega(+1, 4, 5),
>     Omega(+1, 4, 3),
>     Omega(+1, 8, 5),
>     Omega(+1, 8, 3),
>     Omega(0, 5, 5),
>     Omega(0, 5, 3),
> ];;

# Test
gap> for i in [1 .. Length(data)] do
>     RECOG.TestGroup(altGroups[i], false, Factorial(data[i, 1])/2);
>     RECOG.TestGroup(symGroups[i], false, Factorial(data[i, 1]));
> od;
gap> for i in [1 .. Length(altMatGroups)] do
>     RECOG.TestGroup(altMatGroups[i], false, Size(altMatGroups[i]));
> od;
gap> for i in [1 .. Length(altMatGroups)] do
>     RECOG.TestGroup(altMatGroups[i], true, Size(altMatGroups[i]));
> od;
gap> for i in [1 .. Length(nonAltOrSymGroups)] do
>     if FindHomMethodsGeneric.SnAnUnknownDegree(RecogNode(nonAltOrSymGroups[i]), nonAltOrSymGroups[i]) = Success then
>         Print("ERROR: Recognised group [", i, "] wrongly as Sn/An!\n");
>     fi;
> od;

# RECOG.IsFixedPoint
gap> ri := RecogNode(SymmetricGroup(10));;
gap> g := (1,2,3,4,5,6,7,8);;
gap> c := (1,2,3);;
gap> r := (1,2)(4,5,6);;
gap> RECOG.IsFixedPoint(ri, g,c,r);
true
gap> r := (2,3,4);;
gap> RECOG.IsFixedPoint(ri, g,c,r);
false

# RECOG.AdjustCycle
gap> ri := RecogNode(SymmetricGroup(10));;
gap> g := (1,2,3,4,5,6,7,8);;
gap> c := (1,2,3);;
gap> r := (4,5);;
gap> RECOG.AdjustCycle(ri, g, c, r, 8);
(3,5)
gap> r := (3,4,5);;
gap> RECOG.AdjustCycle(ri, g, c, r, 8);
(3,4,5)
gap> r := (2,5);;
gap> RECOG.AdjustCycle(ri, g, c, r, 8);
(3,5)
gap> r := (2,4,5);;
gap> RECOG.AdjustCycle(ri, g, c, r, 8);
(3,5,4)
gap> r := (2,3,5);;
gap> RECOG.AdjustCycle(ri, g, c, r, 8);
(3,4,5)
gap> r := (1,5);;
gap> RECOG.AdjustCycle(ri, g, c, r, 8);
(3,5)
gap> r := (1,4,5);;
gap> RECOG.AdjustCycle(ri, g, c, r, 8);
(3,5,4)
gap> r := (1,3,4,5);;
gap> RECOG.AdjustCycle(ri, g, c, r, 8);
(3,6,4,5)
gap> r := (1,2,5);;
gap> RECOG.AdjustCycle(ri, g, c, r, 8);
(3,5,4)
gap> r := (1,2,3,5);;
gap> RECOG.AdjustCycle(ri, g, c, r, 8);
(3,5,4,6)

# RECOG.BuildCycle
gap> ri := RecogNode(SymmetricGroup(10));;

# c = (u,v,w)
gap> c := (1,2,3);;

# Form 1: x = (v,a_1,...,a_alpha) * (w,b_1,....,b_beta) * (...)
# alpha - beta = 0
gap> x := (2,4,5,6)* (3,7,8,9);;
gap> RECOG.BuildCycle(ri, c, x, 10);
[ (1,2,3,4,7,5,8,6,9), 9 ]

# alpha - beta = -1
gap> x := (2,4,5,6)* (3,7,8,9,10);;
gap> RECOG.BuildCycle(ri, c, x, 10);
[ (1,2,3,4,7,5,8,6,9), 9 ]

# alpha - beta = 1
gap> x := (2,4,5,6,10)* (3,7,8,9);;
gap> RECOG.BuildCycle(ri, c, x, 10);
[ (1,2,3,4,7,5,8,6,9), 9 ]

# alpha - beta = -2
gap> x := (2,4,5) * (3,7,8,9,10);;
gap> RECOG.BuildCycle(ri, c, x, 10);
[ (1,2,3,4,7,5,8,10,9), 9 ]

# alpha - beta = 2
gap> x := (2,4,5,6,10) * (3,7,8);;
gap> RECOG.BuildCycle(ri, c, x, 10);
[ (1,2,3,4,7,5,8,6,10), 9 ]

# Form 2: x = (v,a_1,...,a_alpha,w,b_1,....,b_beta) * (...)
# alpha - beta = 0
gap> x := (2,4,5,6,3,7,8,9);;
gap> RECOG.BuildCycle(ri, c, x, 10);
[ (1,2,3,4,7,5,8,6,9), 9 ]

# alpha - beta = -1
gap> x := (2,4,5,6,3,7,8,9,10);;
gap> RECOG.BuildCycle(ri, c, x, 10);
[ (1,2,3,4,7,5,8,6,9), 9 ]

# alpha - beta = 1
gap> x := (2,4,5,6,10,3,7,8,9);;
gap> RECOG.BuildCycle(ri, c, x, 10);
[ (1,2,3,4,7,5,8,6,9), 9 ]

# alpha - beta = -2
gap> x := (2,4,5,3,7,8,9,10);;
gap> RECOG.BuildCycle(ri, c, x, 10);
[ (1,2,3,4,7,5,8,10,9), 9 ]

# alpha - beta = 2
gap> x := (2,4,5,6,10,3,7,8);;
gap> RECOG.BuildCycle(ri, c, x, 10);
[ (1,2,3,4,7,5,8,6,10), 9 ]

# Construct isomorphism between S_11 on 2-sets and S_11 in natural
# representation.
gap> sets := Combinations([1 .. 11], 2);;
gap> S11On2Sets := Action(SymmetricGroup(11), sets, OnSets);;
gap> ri := RecogNode(S11On2Sets);;
gap> FindHomMethodsGeneric.SnAnUnknownDegree(ri, S11On2Sets);;
gap> isoData := ri!.SnAnUnknownDegreeIsoData;;
gap> gens := GeneratorsOfGroup(S11On2Sets);;
gap> g1 := gens[1];;
gap> img1 := RECOG.FindImageSn(ri, 11, g1, isoData[1][1], isoData[1][2],
>                        isoData[2][1], isoData[2][2]);;
gap> CycleStructurePerm(img1);
[ ,,,,,,,,, 1 ]
gap> g2 := gens[2];;
gap> img2 := RECOG.FindImageSn(ri, 11, g2, isoData[1][1], isoData[1][2],
>                        isoData[2][1], isoData[2][2]);;
gap> CycleStructurePerm(img2);
[ 1 ]

# FindHomMethodsGeneric.SnAnUnknownDegree
# Sn
gap> for d in [11 .. 14] do
> sets := Combinations([1 .. d], 2);;
> SdOn2Sets := Action(SymmetricGroup(d), sets, OnSets);;
> ri := RecogNode(SdOn2Sets);;
> success := FindHomMethodsGeneric.SnAnUnknownDegree(ri, SdOn2Sets);
> if not success or not Size(ri) = Factorial(d) then
>   Print("wrong result! degree ", d, "\n");
> fi;
> od;

# An
gap> for d in [11 .. 14] do
> sets := Combinations([1 .. d], 2);;
> SdOn2Sets := Action(AlternatingGroup(d), sets, OnSets);;
> ri := RecogNode(SdOn2Sets);;
> success := FindHomMethodsGeneric.SnAnUnknownDegree(ri, SdOn2Sets);
> if not success or not Size(ri) = Factorial(d)/2 then
>   Print("wrong result! degree ", d, "\n");
> fi;
> od;

# Check Slp function
gap> ri := RecogNode(S11On2Sets);;
gap> FindHomMethodsGeneric.SnAnUnknownDegree(ri, S11On2Sets);
true
gap> x := PseudoRandom(Grp(ri));;
gap> slp := SLPforElement(ri, x);;
gap> x = ResultOfStraightLineProgram(slp, NiceGens(ri));
true

#
# Remove Hacky injection of our method
gap> for db in [FindHomDbPerm, FindHomDbMatrix, FindHomDbProjective] do
>       Remove(db,
>              PositionProperty(db, x -> Stamp(x.method) = "SnAnUnknownDegree"));;
> od;
