#
gap> START_TEST("presentation.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);;
gap> testPres := function(G, small, projective)
> local ri,iso,pres,F,hom,rel,projG,projString;
> if projective then ri := RecogniseProjectiveGroup(G);; else ri := RecogniseGroup(G);; fi;
> pres := StdPresentation(ri);;
> F := FreeGroupOfFpGroup(pres);;
> hom := GroupHomomorphismByImages(F, G, GeneratorsOfGroup(F), NiceGens(ri));;

# Test that G satisfies all relations in presentation
> for rel in RelatorsOfFpGroup(pres) do
>   if not isone(ri)(hom(rel)) then
>       if projective then projString := " (proj.)";; else projString := "";; fi;
>       Print(G, projString, " does not satisfy relation\n");;
>   fi;;
> od;;

# For small groups, also test that G has same size as presentation
> if small then
>   if projective then
>     projG := Image(ProjectiveActionHomomorphismMatrixGroup(G));;
>   else
>     projG := G;;
>   fi;
>   if Size(projG) <> Size(pres) then
>     Print(G, " does not have same size as FpGroup\n");;
>   fi;
> fi;
> end;;
gap> smallMatGroups := Concatenation([
> List([2,3,4,5,13,17], q -> SL(2,q)),
> List([[3,2],[3,3],[4,2]], l -> SL(l[1], l[2])),
> List([2,3], q -> Sp(4, q)),
> List([2,3,4,5,13,17], q -> SO(3,q)),
> List([2,3,4,5], q -> SO(1,4,q)),
> List([2,3,4,5], q -> SO(-1,4,q))
> ]);;
gap> largeMatGroups := [SL(4,3), Sp(4,7), SO(5,3)];;
gap> permGroups := [SymmetricGroup(5), AlternatingGroup(7)];;

# LowerLeftPGroup leaves should expose a pc presentation with one power
# relation per generator and one conjugation relation per pair.
gap> gens := [];;
gap> for i in [2..3] do
>   m := IdentityMat(3, GF(2));;
>   m[i,i-1] := One(GF(2));;
>   Add(gens, m);
> od;
gap> ri := RecognizeGroup(Group(gens));;
gap> Size(ri);
8
gap> Size(StdPresentation(ri));
8
gap> leaf := GetCompositionTreeNode(ri, "fk");;
gap> std := StdPresentation(leaf);;
gap> Size(std);
8
gap> RelatorsOfFpGroup(StdPresentation(leaf));
[ f1^2, f2^2, f1^-1*f2*f1*f3^-1*f2^-1, f3^2, f1^-1*f3*f1*f3^-1, 
  f2^-1*f3*f2*f3^-1 ]

#
gap> for G in smallMatGroups do testPres(G, true, false); od;
gap> for G in largeMatGroups do testPres(G, false, false); od;
gap> for G in smallMatGroups do testPres(G, true, true); od;
gap> for G in largeMatGroups do testPres(G, false, true); od;
gap> for G in permGroups do testPres(G, true, false); od;

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("presentation.tst");
