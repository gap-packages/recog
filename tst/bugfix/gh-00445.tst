gap> START_TEST("gh-00445.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);

# Issue #445: cross-characteristic PSL2 low-index hints must fail quickly
# and allow recognition to continue, instead of exhausting a huge random
# search and raising an internal error.
# See https://github.com/gap-packages/recog/issues/445
gap> G:=Group(Z(7)^0*[   # this group is ClassicalMaximals("L",6,7)[21];
> [[2,5,0,2,1,0],
>  [1,4,0,4,3,0],
>  [6,5,1,2,3,0],
>  [5,0,0,1,2,0],
>  [3,5,0,2,0,0],
>  [2,6,0,1,6,1]],
> [[3,6,5,3,6,1],
>  [0,3,4,1,2,0],
>  [6,3,0,6,6,0],
>  [4,3,0,4,0,0],
>  [0,6,5,3,0,0],
>  [0,0,4,1,1,6]],
> [[3,0,0,0,0,0],
>  [0,3,0,0,0,0],
>  [0,0,3,0,0,0],
>  [0,0,0,3,0,0],
>  [0,0,0,0,3,0],
>  [0,0,0,0,0,3]]
> ]);;
gap> i := 44;; Reset(GlobalRandomSource, i);; Reset(GlobalMersenneTwister, i);;
gap> ri := RecognizeGroup(G);;
gap> IsReady(ri);
true
gap> ForAll(GeneratorsOfGroup(G), x -> SLPforElement(ri, x) <> fail);
true

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("gh-00445.tst");
