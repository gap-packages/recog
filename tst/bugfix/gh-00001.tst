gap> START_TEST("gh-00001.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);

# See https://github.com/gap-packages/recog/issues/1
gap> gens := [];; e:=Z(2)^0;;
gap> mat:=IdentityMat(4,GF(2));; mat[1,2]:=e;; Add(gens, mat);
gap> mat:=IdentityMat(4,GF(2));; mat[2,1]:=e;; Add(gens, mat);
gap> mat:=IdentityMat(4,GF(2));; mat[3,2]:=e;; Add(gens, mat);
gap> mat:=IdentityMat(4,GF(2));; mat[4,3]:=e;; Add(gens, mat);
gap> G:=Group(gens);
<matrix group with 4 generators>
gap> ri:=RECOG.TestGroup(G, false, 192);;
gap> outsider:=Reversed(IdentityMat(4,GF(2)));;
gap> outsider in ri;
false

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("gh-00001.tst");
