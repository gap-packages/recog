gap> START_TEST("gh-00065.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);

# See https://github.com/gap-packages/recog/issues/65
gap> RecogniseGroup(SL(2,2));
<recognition node GoProjective Dim=2 Field=2
 F:<recognition node (projective) ClassicalNatural Comment=PSL2 Size=6 Dim=
2 Field=2>
 K:<trivial kernel>
gap> RecogniseGroup(SL(2,3));
<recognition node GoProjective Dim=2 Field=3
 F:<recognition node (projective) ClassicalNatural Comment=PSL2 Size=12 Dim=
2 Field=3>
 K:<recognition node DiagonalMatrices Dim=2 Field=3
    F:<recognition node Scalar Dim=1 Field=3>
    K:<trivial kernel>>
gap> RecogniseGroup(SL(2,4));
<recognition node GoProjective Dim=2 Field=4
 F:<recognition node (projective) ClassicalNatural Comment=PSL2 Simple Size=
60 Dim=2 Field=4>
 K:<trivial kernel>
gap> RecogniseGroup(SL(2,5));
<recognition node GoProjective Dim=2 Field=5
 F:<recognition node (projective) ClassicalNatural Comment=PSL2 Simple Size=
60 Dim=2 Field=5>
 K:<recognition node DiagonalMatrices Dim=2 Field=5
    F:<recognition node Scalar Dim=1 Field=5>
    K:<trivial kernel>>

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("gh-00065.tst");
