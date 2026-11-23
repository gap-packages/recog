gap> START_TEST("gh-00133.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);

# Issue #133: RECOG.simplesocle on an abelian group would get stuck in an infinite loop
gap> G := Group([DiagonalMatrix(Z(3)*[1,2]), DiagonalMatrix(Z(3)*[2,1])]);;
gap> ri:=RecogNode(G,true,rec());;
gap> ForAll([1..100], i -> RECOG.simplesocle(ri,G) = fail);
true

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("gh-00133.tst");
