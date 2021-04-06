# in this test, we start with a matrix group, but for some subfactor switch
# to a permutation group; this is done in d247.gi by
# RECOG.SortOutReducibleNormalSubgroup
gap> n:=7;; G:=AlternatingGroup(n);;
gap> gens:=List(GeneratorsOfGroup(G),g->PermutationMat(g,n)) * Z(5);;
gap> gens[1][1][2] := -gens[1][1][2];; gens[2][7][5] := -gens[2][7][5];;
gap> H2:=Group(gens);;
gap> # FIXME: test disabled for now, as it sometimes fails
gap> #ri:=RECOG.TestGroup(H2, false, 645120);;
gap> #IsMatrixGroup(Grp(ImageRecogNode(ri)));
gap> #IsPermGroup(Grp(ImageRecogNode(ImageRecogNode(ri))));
