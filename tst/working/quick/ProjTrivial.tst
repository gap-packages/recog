gap> g := GroupWithGenerators([One(GL(7,5))]);;
gap> gens := ShallowCopy(GeneratorsOfGroup(g));;
gap> repeat r := Random(GF(5)); until not(IsZero(r));
gap> Add(gens,gens[1]*r);;
gap> g := GroupWithGenerators(gens);;
gap> ri := RECOG.TestGroup(g,true,1,rec(tryNonGroupElements := true));;
