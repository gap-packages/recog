gap> START_TEST("goingup.tst");
gap> Reset(GlobalMersenneTwister, 1);;
gap> Reset(GlobalRandomSource, 1);;

# The root elements of RECOG.SL_RootElements are the elementary matrices
# they name.
gap> CheckSLRoots := function(n, q)
>     local f, Y, R, i, j, lambda, M;
>     f := GF(q);
>     Y := GeneratorsWithMemory(
>              RECOG.ClassicalStandardGenerators("SL", n, f).all);
>     R := RECOG.SL_RootElements(Y, n, f);
>     for i in [1 .. n] do
>         for j in Difference([1 .. n], [i]) do
>             lambda := Random(f);
>             M := MutableCopyMat(IdentityMat(n, f));
>             M[i, j] := lambda;
>             if StripMemory(RECOG.SL_ElementaryMatrix(R, i, j, lambda)) <> M
>                then
>                 return [i, j, lambda];
>             fi;
>         od;
>     od;
>     return true;
> end;;
gap> ForAll([[2, 3], [3, 4], [4, 9], [5, 2], [6, 25], [7, 27]],
>           c -> CheckSLRoots(c[1], c[2]) = true);
true

# The eliminations map vectors to the basis vectors they promise, also
# vectors with few nonzero coordinates, which take the rarer branches.
gap> CheckEliminations := function(n, q)
>     local f, e, R, vecs, y, b;
>     f := GF(q);
>     e := IdentityMat(n, f);
>     vecs := Concatenation(e, List([1 .. 20], i -> Random(f^n)),
>                           List([2 .. n], i -> e[i] + e[1]));
>     vecs := Filtered(vecs, y -> not IsZero(y));
>     R := RECOG.SL_RootElements(GeneratorsWithMemory(
>              RECOG.ClassicalStandardGenerators("SL", n, f).all), n, f);
>     for y in vecs do
>         b := RECOG.SL_MapToLast(R, y);
>         if y * b.mat <> e[n] or StripMemory(b.word) <> b.mat then
>             return ["SL", y];
>         fi;
>     od;
>     return true;
> end;;
gap> ForAll([[4, 3], [5, 4], [6, 5], [8, 9], [4, 25], [6, 81]],
>           c -> CheckEliminations(c[1], c[2]) = true);
true
gap> CheckExpress := function(n, q)
>     local f, R, E;
>     f := GF(q);
>     R := RECOG.SL_RootElements(GeneratorsWithMemory(
>              RECOG.ClassicalStandardGenerators("SL", n, f).all), n, f);
>     E := {i, j, lambda} -> RECOG.SL_ElementaryMatrix(R, i, j, lambda);
>     return ForAll([1 .. 5], function(k)
>         local M;
>         M := PseudoRandom(SL(n, q));
>         return StripMemory(RECOG.SL_ExpressByElementary(M, E, R.one)) = M;
>     end);
> end;;
gap> ForAll([[2, 5], [3, 2], [5, 9]], c -> CheckExpress(c[1], c[2]));
true

# RECOG.GoingUp, started from the standard generators of an embedded
# CL(n,q), returns words for the standard generators of CL(d,q) relative
# to the basis it returns.
gap> CheckGoingUp := function(type, n, d, q)
>     local f, B, init, std, gens, G, res;
>     f := GF(q);
>     B := RandomInvertibleMat(d, f);
>     init := List(RECOG.ClassicalStandardGenerators(type, n, f).all,
>                  x -> B^-1 * RECOG.GoingUpEmbed(x, d, f) * B);
>     std := RECOG.ClassicalStandardGenerators(type, d, f).all;
>     gens := Concatenation(init, List(std, x -> B^-1 * x * B));
>     G := GroupWithMemory(Group(gens));
>     res := RECOG.GoingUp(G, type,
>                rec( slp := StraightLineProgram(
>                                [List([1 .. Length(init)], i -> [i, 1])],
>                                Length(gens)),
>                     bas := B, n := n ));
>     return List(ResultOfStraightLineProgram(res.slp, gens),
>                 x -> res.bas * x * res.bas^-1) = std;
> end;;
gap> ForAll([["SL", 2, 3, 7], ["SL", 2, 8, 4], ["SL", 2, 17, 5],
>            ["SL", 2, 12, 9]],
>           c -> CallFuncList(CheckGoingUp, c));
true

#
gap> STOP_TEST("goingup.tst");
