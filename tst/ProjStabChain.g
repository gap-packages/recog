# ProjStabChain:
# Usage: ReadPackage("recog","tst/ProjStabChain.g");
LoadPackage("recog");
ReadPackage("recog","tst/products.g");
gens := AtlasGenerators("HS",9).generators;
g := GroupWithGenerators(gens);
Print("Testing ProjStabChain:\n");
ri := RECOG.TestGroup(g,true,44352000);
Print("\n");
