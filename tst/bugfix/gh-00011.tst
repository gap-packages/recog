gap> START_TEST("gh-00011.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);

# Issue #11.
gap> G1 := Group(Z(3)^0 * [ [[1,0,0],[0,1,0],[0,0,-1]], [[1,-1,-1],[0,0,1],[0,-1,0]] ]);;
gap> for i in [1..50] do
>     ri := RECOG.TestGroup(G1, false, 72);
> od;

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("gh-00011.tst");
