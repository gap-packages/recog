gap> ag := AtlasGenerators([ "HS", [ "HSG1-f2r20B0.m1", "HSG1-f2r20B0.m2" ], 1, 2 ]);;
gap> g := Group(ag.generators);;
gap> ri := RECOG.TestGroup(g,true,ag.size);;

# An orbit longer than the limit of genss must not raise an error
gap> limit := GENSS.OrbitLengthLimit;;
gap> GENSS.OrbitLengthLimit := 100;;
gap> level := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);
gap> levelMethSel := InfoLevel(InfoRecog_MethSel);;
gap> SetInfoLevel(InfoRecog_MethSel, 0);
gap> ri := RecogNode(Omega(7,3), true);;
gap> FindHomMethodsProjective.StabilizerChainProj(ri) = NeverApplicable;
true
gap> ri := RecogniseProjectiveGroup(Omega(7,3));;
gap> IsReady(ri);
false
gap> SetInfoLevel(InfoRecog_MethSel, levelMethSel);
gap> SetInfoLevel(InfoRecog, level);
gap> GENSS.OrbitLengthLimit := limit;;
