#@local testFunction, degrees
#@local altGroups, symGroups, permMatGroup, altMatGroups, nonAltOrSymGroups
#@local ri, g, c, r, i, x
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