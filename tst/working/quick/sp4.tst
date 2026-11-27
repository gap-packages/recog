gap> START_TEST("sp4.tst");
gap> oldInfoLevel := InfoLevel(InfoOrb);;
gap> SetInfoLevel(InfoOrb, 0); # the stabiliser chain reports orbit sizes
gap> Reset(GlobalMersenneTwister, 1);;
gap> Reset(GlobalRandomSource, 1);;

# RECOG.Sp_FinalDescent must express the standard generators of an Sp(4,q)
# in Sp(n,q) as straight line programs in the given generators. Relative to
# the basis it returns, they are those of RECOG.ClassicalStandardGenerators,
# extended by the identity, and its first four rows are a standard basis of
# a multiple of the form. Sp(n,3) is recognised by a stabiliser chain.
gap> CheckSp_FinalDescent := function(n, q)
>     local f, G, gens, res, std, form;
>     f := GF(q);
>     G := Sp(n, q)^PseudoRandom(GL(n, q));
>     gens := GeneratorsOfGroup(G);
>     res := RECOG.Sp_FinalDescent(gens, f);
>     std := List(RECOG.ClassicalStandardGenerators("Sp", 4, f).all,
>                 x -> DirectSumMat(x, IdentityMat(n - 4, f)));
>     form := MTX.InvariantBilinearForm(GModuleByMats(gens, f));
>     form := (res.bas * form * TransposedMat(res.bas)){[1..4]}{[1..4]};
>     return List(ResultOfStraightLineProgram(res.slp, gens),
>                 g -> res.bas * g * res.bas^-1) = std
>            and form = form[1, 2] * RECOG.ClassicalStandardForm("Sp", 4, f);
> end;;
gap> Filtered([3, 5, 7, 9, 11, 13, 25, 27, 49, 81, 125, 243],
>             q -> not CheckSp_FinalDescent(4, q));
[  ]
gap> Filtered([[6, 3], [6, 5], [6, 9], [8, 3], [8, 7], [8, 27]],
>             args -> not CallFuncList(CheckSp_FinalDescent, args));
[  ]

#
gap> SetInfoLevel(InfoOrb, oldInfoLevel);
gap> STOP_TEST("sp4.tst");
