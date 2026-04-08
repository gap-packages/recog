gap> START_TEST("sl2.tst");
gap> testConRecogNaturalSL2 := function(q)
>   local G, list, res, f, i, std;
>   f := GF(q);
>   list := [];
>   for i in [1..10] do
>     Add(list, Random(SL(2,q)));
>   od;
>   G := GroupWithGenerators(list);
>   res := RECOG.RecogniseSL2Natural(G,f);
>   std := RECOG.MakeSL_StdGens(Characteristic(f),DegreeOverPrimeField(f),2,2);
>   for i in [1..Length(res.all)] do
>     if res.all[i]^res.basi <> std.all[i] then
>       return false;
>     fi;
>   od;
>   return true;
> end;;
gap> testConRecogNaturalSL22 := function()
>   local G, list, res, f, i, j, std;
>   f := GF(2);
>   std := RECOG.MakeSL_StdGens(2, 1, 2, 2);
>   for j in [1..50] do
>     repeat
>       list := List([1..10], i -> Random(SL(2,2)));
>       G := GroupWithGenerators(list);
>     until Size(G) = 6;
>     res := RECOG.RecogniseSL2Natural2(G, f);
>     for i in [1..Length(res.all)] do
>       if StripMemory(res.all[i])^res.basi <> std.all[i] then
>         Print("FAILED at index ", i, "\n");
>         return false;
>       fi;
>     od;
>   od;
>   return true;
> end;;
gap> testConRecogNaturalSL25 := function()
>   local f, j, list, G, res, u1, l1, m, id;
>   f := GF(5);
>   for j in [1..50] do
>     list := List([1..15], i -> Random(SL(2,5)));
>     G := GroupWithGenerators(list);
>     res := RECOG.RecogniseSL2Natural5(G,f);
>     u1 := [[Z(5)^0,Z(5)^0],[0*Z(5)^0,Z(5)^0]];
>     l1 := [[Z(5)^0,0*Z(5)^0],[Z(5)^0,Z(5)^0]];
>     m := [[0*Z(5)^0,Z(5)^2],[Z(5)^0,0*Z(5)^0]];
>     id := [[Z(5)^0,0*Z(5)^0],[0*Z(5)^0,Z(5)^0]];‚
>       if res.all[1]^res.basi <> u1 or res.all[2]^res.basi <> l1 or res.all[3]^res.basi <> m or res.all[4]^res.bas <> id then
>         Print("FAILED\n", j,"\n");
>         return false;
>       fi;
>   od;
>   return true;
> end;;
gap> list := Filtered([2..1000], IsPrimePowerInt);;
gap> for q in list do
>   if not testConRecogNaturalSL2(q) then
>     Print("FAILED for q = ", q, "\n");
>   fi;
> od;
gap> if not testConRecogNaturalSL22() then
>   Print("FAILED for SL(2,2)\n");
> fi;
gap> if not testConRecogNaturalSL25() then
> Print("FAILED for SL(2,5)\n");
> fi;
gap> STOP_TEST("sl2.tst");
