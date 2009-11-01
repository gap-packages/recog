# MatAn
# Usage: ReadPackage("recog","tst/MatAn.g");
LoadPackage("recog");
gens := List(GeneratorsOfGroup(AlternatingGroup(51)),
             x->PermutationMat(x,51,GF(3)));
m := GModuleByMats(gens,GF(3));
cf := MTX.CompositionFactors(m);
pos := First([1..2],x->cf[x].dimension=49);
gens := cf[pos].generators;
g := Group(gens);
g := Group(List([1..10],x->PseudoRandom(g)));
Print("Testing MatAn:\n");
ri := RECOG.TestGroup(g,false,Factorial(51)/2);
Print("\n");

