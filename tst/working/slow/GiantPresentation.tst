#
gap> START_TEST("GiantPresentation.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);;
gap> testGiantPres := function(n, stamp, checkSize)
>  local size, giant, giantGens, pres, F, hom, rel;
>  if stamp = "Sn" then
>    size := Factorial(n);
>    giant := SymmetricGroup(n);
>    giantGens := RECOG.SnNiceGens(n);
>    pres := RECOG.SnPresentation(n);
>  elif stamp = "An" then
>    if n=1 then
>      size := 1;
>    else
>      size := Factorial(n)/2;
>    fi;
>    giant := AlternatingGroup(n);
>    giantGens := RECOG.AnNiceGens(n);
>    pres := RECOG.AnPresentation(n);
>  else
>    Print("Incorrect argument for test function\n");
>  fi;
>  if checkSize and Size(pres) <> size then
>    Print("Presentation for ", stamp, ", n=", n, ", has incorrect size\n");
>  fi;
>  F := FreeGroupOfFpGroup(pres);
>  hom := GroupHomomorphismByImages(F, giant, GeneratorsOfGroup(F), giantGens);
>  for rel in RelatorsOfFpGroup(pres) do
>    if not IsOne(hom(rel)) then
>      Print(stamp, ", for n=", n, ", does not satisfy the relations of StdPresentation\n");
>    fi;
>  od;
> end;;
gap> for n in [1..10] do testGiantPres(n, "Sn", true); od;;
gap> for n in [1..10] do testGiantPres(n, "An", true); od;;
gap> for n in [11..20] do testGiantPres(n, "Sn", false); od;;
gap> for n in [11..20] do testGiantPres(n, "An", false); od;;

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("GiantPresentation.tst");
