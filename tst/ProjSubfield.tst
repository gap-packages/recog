gap> h := GL(4,3^2);;
gap> x := PseudoRandom(GL(4,3^4));;
gap> gens := List(GeneratorsOfGroup(h),y->y^x);;
gap> g := GroupWithGenerators(gens);;
gap> ri := RECOG.TestGroup(g,true,Size(PGL(4,3^2)));;
