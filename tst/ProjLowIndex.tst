gap> ReadPackage("recog","tst/products.g");;
gap> gens := [[[Z(7)]],[[Z(7)^0]]];;
gap> g := GroupWithGenerators(gens);;
gap> g := WreathProductOfMatrixGroup(g,SymmetricGroup(5));;
gap> ri := RECOG.TestGroup(g,true,155520);;
