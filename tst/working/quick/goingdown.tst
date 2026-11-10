gap> START_TEST("goingdown.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);
gap> Reset(GlobalMersenneTwister, 1);;
gap> Reset(GlobalRandomSource, 1);;

# RECOG.FindStingrayElement returns m-stingray elements: s fixes a
# subspace of codimension m and its characteristic polynomial is
# (x-1)^(d-m) times an irreducible polynomial of degree m.
gap> IsStingray := function(s, m)
>     local cp;
>     s := StripMemory(s);
>     cp := Collected(Factors(CharacteristicPolynomial(s)));
>     return Length(RECOG.FixspaceMat(s)) = NrRows(s) - m and Length(cp) = 2
>            and ForAny(cp, c -> Degree(c[1]) = m and c[2] = 1);
> end;;
gap> params := RECOG.GoingDownParameters("SL", 7);;
gap> D := RECOG.StingrayBodyDimensions(30, params);
[ 2 .. 10 ]
gap> G := GroupWithMemory(SL(30, 7));;
gap> ForAll([1..10], function(i)
>      local r;
>      r := RECOG.FindStingrayElement(G, D, 100);
>      return r <> fail and r.dim in D and IsStingray(r.element, r.dim);
>    end);
true

# RECOG.GoingDown returns SLPs for generators of SL(4,q) and a basis in
# which their lifts are block diagonal with an identity block.
gap> CheckGoingDown := function(d, q)
>     local G, down, x;
>     G := GroupWithMemory(SL(d, q)^PseudoRandom(GL(d, q)));
>     down := RECOG.GoingDown(G, "SL", RECOG.GoingDownRandomBound);
>     x := ResultOfStraightLineProgram(down.slp,
>                                      StripMemory(GeneratorsOfGroup(G)));
>     return Length(down.gens[1]) = 4 and
>            ForAll([1..Length(x)], i -> down.bas * x[i] * down.bas^-1
>                = DirectSumMat(down.gens[i], IdentityMat(d - 4, GF(q))))
>            and RecogniseClassical(Group(down.gens)).isSLContained = true;
> end;;
gap> List([[5, 2], [9, 3], [20, 5], [33, 4], [40, 121]],
>         args -> CallFuncList(CheckGoingDown, args));
[ true, true, true, true, true ]

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("goingdown.tst");
