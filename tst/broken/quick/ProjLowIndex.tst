# See https://github.com/gap-packages/recog/issues/101
gap> ReadPackage("recog","tst/products.g");;
gap> gens := [[[Z(7)]],[[Z(7)^0]]];;
gap> g := GroupWithGenerators(gens);;
gap> h := WreathProductOfMatrixGroup(g,SymmetricGroup(5));;

# let's compute the expected size of h
gap> Size(g)^5 * Factorial(5);
933120

#
gap> ri := RECOG.TestGroup(h,true,933120);;
