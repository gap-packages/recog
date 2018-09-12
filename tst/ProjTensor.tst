gap> ReadPackage("recog","tst/products.g");;
gap> g := GL(4,5);;
gap> h := SL(6,5);;
gap> k := TensorProductOfMatrixGroup(g,h);;
gap> ri := RECOG.TestGroup(k,true,Size(PGL(4,5))*Size(PSL(6,5)));;
Test was OK!
..............................
30 random elements successfully sifted!
