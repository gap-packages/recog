gap> START_TEST("gh-00317.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);

# Issue #317: false PSL2 recognition must fall back cleanly instead of
# reaching invalid determinant-root normalization or late verification errors.
# See https://github.com/gap-packages/recog/issues/317
gap> G := Group(Z(5)^0*[
>   [ [ 0, 2, 0, 2 ], [ 1, 4, 4, 4 ], [ 0, 4, 0, 0 ], [ 3, 2, 0, 0 ] ],
>   [ [ 0, 2, 0, 2 ], [ 4, 4, 1, 4 ], [ 0, 1, 0, 0 ], [ 3, 3, 0, 0 ] ],
>   [ [ 1, 0, 0, 0 ], [ 0, 4, 0, 0 ], [ 0, 0, 4, 0 ], [ 0, 0, 0, 1 ] ],
>   [ [ 2, 0, 0, 0 ], [ 0, 2, 0, 0 ], [ 0, 0, 2, 0 ], [ 0, 0, 0, 2 ] ],
>   [ [ 0, 0, 0, 1 ], [ 0, 2, 0, 0 ], [ 0, 0, 1, 0 ], [ 2, 0, 0, 0 ] ]
> ]);;
gap> i := 115;; Reset(GlobalMersenneTwister, i);; Reset(GlobalRandomSource, i);;
gap> ri := RecognizeGroup(G);;
gap> IsReady(ri);
true
gap> ForAll(GeneratorsOfGroup(G), x -> SLPforElement(ri, x) <> fail);
true
gap> i := 9;; Reset(GlobalRandomSource, i);; Reset(GlobalMersenneTwister, i);;
gap> H := ClassicalMaximals("L",4,7)[4];;
gap> ri := RecognizeGroup(H);;
gap> IsReady(ri);
true
gap> ForAll(GeneratorsOfGroup(H), x -> SLPforElement(ri, x) <> fail);
true

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("gh-00317.tst");
