#
gap> START_TEST("GiantPresentation.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);;
gap> testGiantPres := function(n, stamp)
>  local size, giant, grp, ri, Fp, F, hom, rel;
>  if stamp = "Sn" then
>    size := Factorial(n);
>    giant := SymmetricGroup;
>  elif stamp = "An" then
>    size := Factorial(n)/2;
>    giant := AlternatingGroup;
>  else
>    Display("Incorrect argument for test function");
>  fi;
>  grp := giant(n);
>  ri := TryFindHomMethod(grp, FindHomMethodsPerm.Giant, false);
>  if not HasStdPresentation(ri) then
>    Display("StdPresentation was not set for ", stamp, ", n=", n);
>  fi;
>  Fp := StdPresentation(ri);
>  if Size(Fp) <> size then
>    Display("StdPresentation for ", stamp, ", n=", n, ", has incorrect size");
>  fi;
>  F := FreeGroupOfFpGroup(Fp);
>  hom := GroupHomomorphismByImages(F, grp, GeneratorsOfGroup(F), NiceGens(ri));
>  for rel in RelatorsOfFpGroup(Fp) do
>    if not IsOne(hom(rel)) then
>      Display(stamp, ", for n=", n, ", does not satisfy the relations of StdPresentation");
>    fi;
>  od;
> end;;
gap> for n in [8..10] do testGiantPres(n, "Sn"); od;;
gap> for n in [8..10] do testGiantPres(n, "An"); od;;

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("GiantPresentation.tst");
