gap> gens := List(GeneratorsOfGroup(SymmetricGroup(30)),
>                 x->PermutationMat(x,30,GF(2)));;
gap> m := GModuleByMats(gens,GF(2));;
gap> cf := MTX.CompositionFactors(m);;
gap> gens := cf[2].generators;;
gap> g := Group(gens);;
gap> g := Group(List([1..10],x->PseudoRandom(g)));;
gap> ri := RECOG.TestGroup(g,false,Factorial(30));;
