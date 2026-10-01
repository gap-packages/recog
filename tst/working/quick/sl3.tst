gap> G:=Group([
>   [ [ Z(25)^20, Z(25)^8, Z(25)^23 ],
>     [ Z(25)^20, Z(25), Z(25)^16 ],
>     [ Z(25)^21, Z(25)^23, Z(25)^13 ] ],
>   [ [ Z(25)^16, Z(25)^0, Z(25)^4 ],
>     [ Z(25)^14, Z(25)^4, Z(25)^19 ],
>     [ Z(25)^23, Z(25)^17, Z(25)^12 ] ]
> ]);;
gap> 
gap> #
gap> ri := RECOG.TestGroup(G, false, 152334000000);;
gap> 
gap> SetInfoLevel(InfoRecog,0);
gap> for q in [ 7, 13, 17, 1009] do
>     G := SL(3,q);
>     H := RECOG.FindSL2inSL3(G,q);
>     if Size(RecognizeGroup(H)) <> Size(SL(2,q)) then
>         Print("FAILED for q = ", q, "\n");
>     fi;
> od;