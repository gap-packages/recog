gap> START_TEST("gh-00466.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);

# Issue #466: ComputeSimpleSocle must give up on non-almost-simple input
# instead of looping forever in its random search for a nontrivial element
# of the third derived subgroup.
# See https://github.com/gap-packages/recog/issues/466
gap> z:=Z(3^2);; G:=Group(z^0 *
> [ [ [ z^2, 0, 0, 0 ], [ 0, z^2, 0, 0 ], [ 0, 0, z^2, 0 ], [ 0, 0, 0, z^2 ] ],
>   [ [ 1, 0, 0, 0 ], [ 0, 2, 0, 0 ], [ 0, 0, 1, 0 ], [ 0, 0, 0, 2 ] ],
>   [ [ 1, 0, 0, 0 ], [ 0, 1, 0, 0 ], [ 0, 0, 2, 0 ], [ 0, 0, 0, 2 ] ],
>   [ [ 0, 1, 0, 0 ], [ 1, 0, 0, 0 ], [ 0, 0, 0, 1 ], [ 0, 0, 1, 0 ] ],
>   [ [ 0, 0, 1, 0 ], [ 0, 0, 0, 1 ], [ 1, 0, 0, 0 ], [ 0, 1, 0, 0 ] ],
>   [ [ z^7, 0, 0, 0 ], [ 0, z, 0, 0 ], [ 0, 0, z^7, 0 ], [ 0, 0, 0, z ] ],
>   [ [ z^7, 0, 0, 0 ], [ 0, z^7, 0, 0 ], [ 0, 0, z, 0 ], [ 0, 0, 0, z ] ],
>   [ [ 1, 1, 0, 0 ], [ 1, 2, 0, 0 ], [ 0, 0, 1, 1 ], [ 0, 0, 1, 2 ] ],
>   [ [ 1, 0, 1, 0 ], [ 0, 1, 0, 1 ], [ 1, 0, 2, 0 ], [ 0, 1, 0, 2 ] ],
>   [ [ z^7, 0, 0, 0 ], [ 0, 0, 0, z^7 ], [ 0, 0, z^7, 0 ], [ 0, z^7, 0, 0 ] ],
> ]);;
gap> i:=279;; Reset(GlobalRandomSource,i);; Reset(GlobalMersenneTwister,i);;
gap> ri:=RecognizeGroup(G);;
gap> IsReady(ri);
true
gap> ri:=RecogNode(G,true,rec());;
gap> CallRecogMethod(FindHomMethodsProjective.ComputeSimpleSocle,ri) <> Success;
true

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("gh-00466.tst");
