#
gap> START_TEST("verification.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> oldInfoOrbLevel := InfoLevel(InfoOrb);;
gap> SetInfoLevel(InfoRecog, 0);;
gap> SetInfoLevel(InfoOrb, 0);;
gap> testGroup := function(G)
>  local numSuccessful, i, ri;
>  numSuccessful := 0;
>  for i in [1..5] do
>    ri := RecogniseGroup(G);
>    if VerifyGroup(ri) = true then
>      numSuccessful := numSuccessful + 1;
>    fi;
>  od;
>  if numSuccessful < 4 then
>    Display(
>       "Verification for ", G, " was succesful only ", numSuccessful,
>       " out of 5 times"
>    );
>  fi;
> end;;

# Test some groups for which verification is expected to work
gap> matGroupList := [
>    SL(2,2), SL(2,3), SL(2,4), SL(2, 9), SL(2,13), SL(2, 53),
>    SL(3,2), SL(3,5), SL(3, 17),
>    SL(5,2), SL(5, 7),
>    Sp(2,2), Sp(2,4), Sp(2,3), Sp(4,2), Sp(4,3), Sp(6,2), Sp(6,3),
>    SO(3,2), SO(3,3), SO(1, 4,2), SO(1, 4,5),
>    Omega(1,4,3)
> ];;
gap> for G in matGroupList do
>  testGroup(G);
> od;
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> SetInfoLevel(InfoOrb, oldInfoOrbLevel);
gap> STOP_TEST("verification.tst");
