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
>    SL(5,2),
>    Sp(2,2), Sp(2,4), Sp(2,3), Sp(4,2), Sp(4,3), Sp(6,2), Sp(6,3),
>    SO(3,2), SO(3,3), SO(1, 4,2), SO(1, 4,5),
>    Omega(1,4,3)
> ];;
gap> for G in matGroupList do
>  testGroup(G);
> od;
gap> permGroupList := [
>    SymmetricGroup(3), SymmetricGroup(5), SymmetricGroup(10),
>    AlternatingGroup(3), AlternatingGroup(8), AlternatingGroup(11),
>    Group((1,2), (3,4)), Group((1,2,3,4))
> ];;
gap> for G in permGroupList do
>  testGroup(G);
> od;

# Input: homomorphism G -> H
# Output: A recognition node for G with (leaf) children K and H where
# K is properly contained in the kernel of homom.
# Sets some attributes of the recognition node, but probably not everything
# that is needed. Work in progress.
gap> createIncorrectRecogNode := function(homom)
>   local G, gensG, H, kern, K, i, g, ri, riF, riK;
>   G := Source(homom);
>   gensG := GeneratorsOfGroup(G);
>   H := Range(homom);
>   kern := Kernel(homom);
>   K := Group(One(G));
>   for i in [1..10] do
>     g := Random(kern);
>     if Order(g) < Size(kern) then
>       K := Group(g);
>       break;
>     fi;
>   od;
>   ri := RecogNode(G);
>   riF := RecogNode(H);
>   riK := RecogNode(K);
>   SetNiceGens(riF, List(gensG, x -> ImageElm(homom, x)));
>   SetNiceGens(riK, GeneratorsOfGroup(K));
>   SetNiceGens(ri, Concatenation(gensG, NiceGens(riK)));
>   SetCalcStdPresentation(riF, CalcStdPresentationGenericLeaf);
>   SetCalcStdPresentation(riK, CalcStdPresentationGenericLeaf);
>   SetCalcStdPresentation(ri, CalcStdPresentationGenericNonLeaf);
>   SetImageRecogNode(ri, riF);
>   SetKernelRecogNode(ri, riK);
>   SetParentRecogNode(riK, ri);
>   SetParentRecogNode(riF, ri);
>   SetHomom(ri, homom);
>   SetFilterObj(riK, IsLeaf);
>   SetFilterObj(riF, IsLeaf);
>   SetFilterObj(riK, IsReady);
>   SetFilterObj(riF, IsReady);
>   SetFilterObj(ri, IsReady);
>   return ri;
> end;;
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> SetInfoLevel(InfoOrb, oldInfoOrbLevel);
gap> STOP_TEST("verification.tst");
