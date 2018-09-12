gap> h := RECOG.MakeC6Group(Sp(4,5),Sp(4,5),3);;
gap> x := PseudoRandom(GL(25,3^4));;
gap> gens := List(GeneratorsOfGroup(h[1]),y->y^x);;
gap> g := GroupWithGenerators(gens);;
gap> ri := RECOG.TestGroup(g,true,5850000000);;
