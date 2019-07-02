gap> h := GL(3,5^2);;
gap> b := Basis(VectorSpace(GF(5),Elements(GF(5^2))));;
gap> gens := List(GeneratorsOfGroup(h),y->BlownUpMat(b,y));;
gap> g := GroupWithGenerators(gens);;
gap> ri := RECOG.TestGroup(g,true,Size(PGL(3,5^2))*6);;
