gap> START_TEST("sun.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);
gap> Reset(GlobalMersenneTwister, 1);;
gap> Reset(GlobalRandomSource, 1);;

# RECOG.FindStdGensSU4 must express the standard generators of SU(4,q) as
# straight line programs in the given generators, with respect to the basis
# it returns, which is a standard basis for a multiple of the form.
gap> CheckFindStdGensSU4 := function(q)
>     local F, G, res, gens, std, form;
>     F := GF(q^2);
>     G := SU(4, q)^PseudoRandom(GL(4, F));
>     res := RECOG.FindStdGensSU4(GeneratorsOfGroup(G), F);
>     gens := ResultOfStraightLineProgram(res.slp, GeneratorsOfGroup(G));
>     std := RECOG.ClassicalStandardGenerators("SU", 4, F).all;
>     form := RECOG.ClassicalInvariantForm("SU", GeneratorsOfGroup(G), F);
>     form := RECOG.FormGram(form, res.bas);
>     return List(gens, g -> res.bas * g * res.bas^-1) = std
>            and form = form[1, 2] * RECOG.ClassicalStandardForm("SU", 4, F);
> end;;
gap> Filtered([3, 5, 7, 9, 11, 13, 25, 27, 49, 81, 121, 243],
>             q -> not CheckFindStdGensSU4(q));
[  ]

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("sun.tst");
