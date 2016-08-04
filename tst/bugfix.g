# See https://github.com/gap-packages/recog/issues/1
gens := []; e:=Z(2)^0;
mat:=IdentityMat(4,GF(2)); mat[1][2]:=e; Add(gens, mat);
mat:=IdentityMat(4,GF(2)); mat[2][1]:=e; Add(gens, mat);
mat:=IdentityMat(4,GF(2)); mat[3][2]:=e; Add(gens, mat);
mat:=IdentityMat(4,GF(2)); mat[4][3]:=e; Add(gens, mat);
G:=Group(gens);
ri:=RECOG.TestGroup(G, false, 192);
outsider:=Reversed(IdentityMat(4,GF(2)));
Assert(0, not outsider in ri);

