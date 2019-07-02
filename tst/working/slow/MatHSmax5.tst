gap> ag := AtlasGenerators([ "HS", [ "HSG1-f2r132B0.m1", "HSG1-f2r132B0.m2" ], 1, 2 ]);;
gap> s := AtlasStraightLineProgram([ "HS", "HSG1-max5W1", 1 ]).program;;
gap> gens := ResultOfStraightLineProgram(s,ag.generators);;
gap> g := Group(gens);;
gap> ri := RECOG.TestGroup(g,false,40320);;
