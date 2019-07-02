gap> ag := AtlasGenerators([ "HS.2", [ "HSd2G1-f3r98aB0.m1", "HSd2G1-f3r98aB0.m2" ], 1, 3 ]);;
gap> g := Group(ag.generators);;
gap> ri := RECOG.TestGroup(g,true,ag.size);;
