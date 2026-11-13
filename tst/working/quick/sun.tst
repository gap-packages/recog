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

# The same for RECOG.FindStdGens_SU and SU(d,q).
gap> CheckFindStdGens_SU := function(d, q)
>     local F, G, res, gens, std, i;
>     F := GF(q^2);
>     G := SU(d, q)^PseudoRandom(GL(d, F));
>     res := RECOG.FindStdGens_SU(G);
>     gens := ResultOfStraightLineProgram(res.slpstd, GeneratorsOfGroup(G));
>     std := RECOG.ClassicalStandardGenerators("SU", d, F).all;
>     for i in [1..Length(std)] do
>         if gens[i]^res.basi <> std[i] then
>             return Concatenation("SU(", String(d), ",", String(q),
>                                  "): generator ", String(i), " is wrong");
>         fi;
>     od;
>     return true;
> end;;
gap> List([[6,3], [8,3], [12,3], [6,5], [8,7], [6,9], [6,13], [10,11],
>          [6,25], [6,27], [24,3]],
>         args -> CallFuncList(CheckFindStdGens_SU, args));
[ true, true, true, true, true, true, true, true, true, true, true ]

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("sun.tst");
