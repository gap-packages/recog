# MatSn
# Usage: ReadPackage("recog","tst/MatSn.g");
LoadPackage("recog");
gens := List(GeneratorsOfGroup(SymmetricGroup(30)),
             x->PermutationMat(x,30,GF(2)));
m := GModuleByMats(gens,GF(2));
cf := MTX.CompositionFactors(m);
gens := cf[2].generators;
g := Group(gens);
g := Group(List([1..10],x->PseudoRandom(g)));
Print("Testing MatSn:\n");
ri := RECOG.TestGroup(g,false,Factorial(30));
Print("\n");

