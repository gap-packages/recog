gap> gens := List(GeneratorsOfGroup(AlternatingGroup(51)),
>               x->PermutationMat(x,51,GF(3)));;
gap> m := GModuleByMats(gens,GF(3));;
gap> cf := MTX.CompositionFactors(m);;
gap> pos := First([1..2],x->cf[x].dimension=49);;
gap> gens := cf[pos].generators;;
gap> g := Group(gens);;
gap> g := Group(List([1..10],x->PseudoRandom(g)));;

# disable the test if cvec is loaded, as it may trigger
# this bug: https://github.com/gap-packages/cvec/issues/18
gap> if not IsPackageMarkedForLoading("cvec","") then
>   ri := RECOG.TestGroup(g,false,Factorial(51)/2);;
> fi;