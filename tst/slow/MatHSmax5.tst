gap> gens := AtlasGenerators("HS",11).generators;;
gap> s := AtlasStraightLineProgram("HS",5).program;;
gap> gens := ResultOfStraightLineProgram(s,gens);;
gap> g := GroupWithGenerators(gens);;
gap> ri := RECOG.TestGroup(g,false,40320);;
