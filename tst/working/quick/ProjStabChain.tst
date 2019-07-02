gap> ag := AtlasGenerators([ "HS", [ "HSG1-f2r20B0.m1", "HSG1-f2r20B0.m2" ], 1, 2 ]);;
gap> g := Group(ag.generators);;
gap> ri := RECOG.TestGroup(g,true,ag.size);;
