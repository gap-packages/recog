gap> TestMatDiagonal := function(F, n)
>     local gens, l, i, m, j, g, ri;
>     gens := [];
>     l := ShallowCopy(Elements(F));
>     RemoveSet(l,Zero(F));
>     for i in [1..5] do
>         m := IdentityMat(7,F);
>         for j in [1..7] do
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
gap> #TestMatDiagonal(GF(9), 7);;  # FIXME: disabled, see issue #36

#
gap> TestMatDiagonal(GF(16), 1);;
gap> TestMatDiagonal(GF(16), 2);;
gap> TestMatDiagonal(GF(16), 3);;
gap> TestMatDiagonal(GF(16), 7);;
