gap> TestMatDiagonal := function(F, n)
>     local gens, l, i, m, j, g, ri;
>     gens := [];
>     l := ShallowCopy(Elements(F));
>     RemoveSet(l,Zero(F));
>     for i in [1..5] do
>         m := IdentityMat(n,F);
>         for j in [1..n] do
>             m[j,j] := Random(l);
>         od;
>         Add(gens,m);
>     od;
>     g := GroupWithGenerators(gens);
>     return RECOG.TestGroup(g,false,Size(g));
> end;;

#
gap> TestMatDiagonal(GF(5), 1);;
gap> TestMatDiagonal(GF(5), 2);;
gap> TestMatDiagonal(GF(5), 3);;
gap> TestMatDiagonal(GF(5), 7);;

#
gap> TestMatDiagonal(GF(9), 1);;
gap> TestMatDiagonal(GF(9), 2);;
gap> TestMatDiagonal(GF(9), 3);;
gap> TestMatDiagonal(GF(9), 7);;

#
gap> TestMatDiagonal(GF(16), 1);;
gap> TestMatDiagonal(GF(16), 2);;
gap> TestMatDiagonal(GF(16), 3);;
gap> TestMatDiagonal(GF(16), 7);;

# A Scalar leaf must store its size: the fallback Size(Grp(ri)) takes
# seconds for a 1x1 matrix group over GF(4099).
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);
gap> z := Z(4099);;
gap> ri := RecognizeGroup(Group([[z^6]], [[z^9]]));;
gap> HasSize(ri);
true
gap> Size(ri);
1366

# The kernel of a BlockScalar node has elements that are words in the lifts
# of the nice generators of the image: here the fourth power of the
# generator. The kernel method has to find them without random elements.
gap> ri := RecogniseGroup(Group(DiagonalMat([ Z(9), Z(9)^2 ])));;
gap> RECOG.FindKernelBlockScalar(ri);
true
gap> Group(StripMemory(gensN(ri))) = Group(DiagonalMat([ Z(3), Z(3)^0 ]));
true
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
