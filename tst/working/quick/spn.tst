gap> START_TEST("spn.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);
gap> Reset(GlobalMersenneTwister, 1);;
gap> Reset(GlobalRandomSource, 1);;

# RECOG.FindStdGens_Sp must express the standard generators of Sp(d,q)
# of RECOG.ClassicalStandardGenerators as straight line programs in the
# given generators, with respect to the basis it returns.
gap> CheckFindStdGens_Sp := function(d, p, ext)
>     local q, G, res, gens, std, i;
>     q := p^ext;
>     G := Sp(d, q)^PseudoRandom(GL(d, q));
>     res := RECOG.FindStdGens_Sp(G);
>     gens := ResultOfStraightLineProgram(res.slpstd, GeneratorsOfGroup(G));
>     std := RECOG.ClassicalStandardGenerators("Sp", d, GF(q)).all;
>     for i in [1..Length(std)] do
>         if gens[i]^res.basi <> std[i] then
>             return Concatenation("Sp(", String(d), ",", String(q),
>                                  "): generator ", String(i), " is wrong");
>         fi;
>     od;
>     return true;
> end;;
gap> List([[4,3,1], [4,5,1], [6,3,1], [6,7,1], [6,3,2], [8,3,1], [12,3,1],
>          [8,5,1], [10,7,1], [14,3,2], [12,11,1]],
>         args -> CallFuncList(CheckFindStdGens_Sp, args));
[ true, true, true, true, true, true, true, true, true, true, true ]

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("spn.tst");
