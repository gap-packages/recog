gap> SetInfoLevel(InfoRecog,0); SetInfoLevel(InfoMethSel,0);
gap> START_TEST("sl4.tst");
gap> testFindSL2inSL4 := function(q)
>   local G, res, h, hb, F;
>   F := GF(q);
>   G := SL(4, q);
>   res := RECOG.FindSL2inSL4(G, 2000);
>   if res = fail then
>     return false;
>   fi;
>   for h in res.gens do
>     hb := res.bas^-1 * h * res.bas;
>     if hb{[3,4]}{[3,4]} <> IdentityMat(2, F) then
>       return false;
>     fi;
>     if hb{[1,2]}{[3,4]} <> NullMat(2, 2, F) then
>       return false;
>     fi;
>     if hb{[3,4]}{[1,2]} <> NullMat(2, 2, F) then
>       return false;
>     fi;
>   od;
>   return true;
> end;;
gap> list := Filtered([3..100], q -> IsPrimePowerInt(q) and q mod 2 = 1);;
gap> for q in list do
>   if not testFindSL2inSL4(q) then
>     Print("FAILED for q = ", q, "\n");
>   fi;
> od;
gap> STOP_TEST("sl4.tst");