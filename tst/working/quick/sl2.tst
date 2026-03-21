gap> START_TEST("sl2.tst");
gap> testConRecogNaturalSL2 := function(q)
>   local G, list, res, f, i, std;
>   f := GF(q);
>   list := [];
>   for i in [1..10] do
>     Add(list, Random(SL(2,q)));
>   od;
>   G := GroupWithGenerators(list);
>   res := RECOG.ConRecogNaturalSL2(G,f);
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
>   if not testConRecogNaturalSL2(q) then
>     Print("FAILED for q = ", q, "\n");
>   fi;
> od;
gap> STOP_TEST("sl2.tst");