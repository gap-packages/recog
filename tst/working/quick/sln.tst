#
gap> START_TEST("sln.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);

# RECOG.FindStdGens_SL must express the standard generators of SL(d,q)
# as straight line programs in the given generators, with respect to the
# basis it returns.  q in [2,3,4,5,9] uses the SL4 base case, the other
# cases go through RECOG.RecogniseSL2Natural.
gap> CheckFindStdGens_SL := function(d, p, ext)
>     local q, G, res, gens, std, i;
>     q := p^ext;
>     G := SL(d, q)^PseudoRandom(GL(d, q));
>     res := RECOG.FindStdGens_SL(G);
>     gens := ResultOfStraightLineProgram(res.slpstd, GeneratorsOfGroup(G));
>     std := RECOG.MakeSL_StdGens(p, ext, d, d).all;
>     for i in [1..Length(std)] do
>         if gens[i]^res.basi <> std[i] then
>             return Concatenation("SL(", String(d), ",", String(q),
>                                  "): generator ", String(i), " is wrong");
>         fi;
>     od;
>     return true;
> end;;
gap> List([[4,3,1], [5,2,1], [4,2,2], [6,3,2], [6,7,1], [7,11,1], [5,2,3], [10,2,1]],
>         args -> CallFuncList(CheckFindStdGens_SL, args));
[ true, true, true, true, true, true, true, true ]

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("sln.tst");
