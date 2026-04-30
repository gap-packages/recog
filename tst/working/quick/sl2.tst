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
gap> STOP_TEST("sl2.tst");
