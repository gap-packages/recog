# See https://github.com/gap-packages/recog/issues/1
gap> gens := [];; e:=Z(2)^0;;
gap> mat:=IdentityMat(4,GF(2));; mat[1,2]:=e;; Add(gens, mat);
gap> mat:=IdentityMat(4,GF(2));; mat[2,1]:=e;; Add(gens, mat);
gap> mat:=IdentityMat(4,GF(2));; mat[3,2]:=e;; Add(gens, mat);
gap> mat:=IdentityMat(4,GF(2));; mat[4,3]:=e;; Add(gens, mat);
gap> G:=Group(gens);
<matrix group with 4 generators>
gap> SetInfoLevel(InfoRecog, 0);
gap> ri:=RECOG.TestGroup(G, false, 192);;
Test was OK!
..............................
30 random elements successfully sifted!
gap> outsider:=Reversed(IdentityMat(4,GF(2)));;
gap> outsider in ri;
false
