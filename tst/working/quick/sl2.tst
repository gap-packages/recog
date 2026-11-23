gap> START_TEST("sl2.tst");
gap> testRecogniseSL2Natural := function(q)
>   local G, res, f, i, std;
>   f := GF(q);
>   G := GroupWithGenerators(List([1..10], i->Random(SL(2,q))));
>   res := RECOG.RecogniseSL2Natural(G,f);
>   std := RECOG.MakeSL_StdGens(Characteristic(f),DegreeOverPrimeField(f),2,2);
>   for i in [1..Length(res.all)] do
>     if res.all[i]^res.basi <> std.all[i] then
>       return false;
>     fi;
>   od;
>   return true;
> end;;
gap> list := Filtered([2..1000], IsPrimePowerInt);;
gap> for q in list do
>   if not testRecogniseSL2Natural(q) then
>     Print("FAILED for q = ", q, "\n");
>   fi;
> od;

# SLPs of the PSL2 leaf evaluate to x on NiceGens, also in a non-standard
# basis and with generators of determinant <> 1
gap> testNiceGensPSL2 := function(q)
>   local c, H, ri, i, x, s;
>   c := Random(GL(2,q));
>   H := Group(List(GeneratorsOfGroup(SL(2,q)), g -> Z(q) * g^c));
>   ri := RecogniseProjectiveGroup(H);
>   if ri!.fhmethsel.successMethod <> "ClassicalNatural" then
>     return fail;
>   fi;
>   for i in [1..10] do
>     x := PseudoRandom(H);
>     s := SLPforElement(ri, x);
>     if s = fail or
>        not isequal(ri)(ResultOfStraightLineProgram(s, NiceGens(ri)), x) then
>       return false;
>     fi;
>   od;
>   return true;
> end;;
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);
gap> List([4, 7, 9, 32], testNiceGensPSL2);
[ true, true, true, true ]
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("sl2.tst");
