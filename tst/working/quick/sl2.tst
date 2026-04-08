gap> START_TEST("sl2.tst");
gap> testRecogniseSL2Natural := function(q)
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
gap> testRecogniseSL2Natural2 := function()
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
gap> testRecogniseSL2Natural4 := function()
>   local G, list, res, f, i, j, std;
>   f := GF(4);
>   std := RECOG.MakeSL_StdGens(2, 2, 2, 2);
>   for j in [1..50] do
>     repeat
>       list := List([1..10], i -> Random(SL(2,4)));
>       G := GroupWithGenerators(list);
>     until Size(G) = 60;
>     res := RECOG.RecogniseSL2Natural4(G, f);
>     for i in [1..Length(res.all)] do
>       if StripMemory(res.all[i])^res.basi <> std.all[i] then
>         Print("FAILED at index ", i, "\n");
>         return false;
>       fi;
>     od;
>   od;
>   return true;
> end;;
gap> list := Filtered([2..1000], IsPrimePowerInt);;
gap> for q in list do
>   if not testRecogniseSL2Natural(q) then
>     Print("FAILED for q = ", q, "\n");
>   fi;
> od;
gap> if not testRecogniseSL2Natural2() then
>   Print("FAILED for SL(2,2)\n");
> fi;
gap> if not testRecogniseSL2Natural4() then
>   Print("FAILED for SL(2,4)\n");
> fi;
gap> STOP_TEST("sl2.tst");
