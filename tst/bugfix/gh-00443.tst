gap> START_TEST("gh-00443.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);

# Issue #443: extension-field scalars modulo base-field scalars should be
# recognized directly, instead of falling through to StabilizerChainProj.
# See https://github.com/gap-packages/recog/issues/443
gap> H:=Group(Z(23)^0*[
>   [ [ 21, 18, 4, 21, 9 ], [ 20, 7, 22, 2, 15 ], [ 18, 12, 6, 11, 15 ],
>       [ 18, 10, 11, 18, 1 ], [ 15, 19, 13, 21, 2 ] ],
>   [ [ 0, 17, 0, 16, 7 ], [ 13, 7, 15, 1, 19 ], [ 9, 9, 18, 21, 19 ],
>       [ 9, 5, 20, 1, 16 ], [ 10, 2, 7, 19, 21 ] ],
>   [ [ 3, 12, 21, 3, 0 ], [ 0, 3, 12, 21, 3 ], [ 22, 3, 12, 19, 19 ],
>       [ 9, 18, 14, 18, 14 ], [ 3, 0, 14, 16, 1 ] ],
>   [ [ 4, 3, 22, 21, 4 ], [ 14, 8, 15, 16, 3 ], [ 22, 17, 17, 22, 14 ],
>       [ 3, 13, 13, 19, 5 ], [ 6, 8, 5, 17, 8 ] ],
>   [ [ 19, 8, 7, 0, 0 ], [ 0, 19, 8, 7, 0 ], [ 0, 0, 19, 8, 7 ],
>       [ 13, 7, 21, 20, 11 ], [ 4, 1, 17, 16, 5 ] ],
> ]);;
gap> ri := RecognizeGroup(H);;
gap> ri;
<recognition node GoProjective Dim=5 Field=23
 F:<recognition node (projective) NotAbsolutelyIrred Dim=5 Field=23
    F:<recognition node (projective) TrivialGroup Size=1 Dim=1 Field=6436343>
    K:<recognition node (projective) BiggerScalarsOnly Size=292561 Dim=
5 Field=23>>
 K:<trivial kernel>
gap> Size(ri);
292561
gap> ForAll(GeneratorsOfGroup(H), x -> SLPforElement(ri, x) <> fail);
true

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("gh-00443.tst");
