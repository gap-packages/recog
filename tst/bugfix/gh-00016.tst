gap> START_TEST("gh-00016.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);

# See https://github.com/gap-packages/recog/issues/16
gap> g := DirectProduct(SymmetricGroup(12),SymmetricGroup(5));;
gap> for i in [1..30] do
>   h:=g^Random(SymmetricGroup(37));
>   r:=RecogniseGroup(h);
>   if Size(r) <> Size(g) then ErrorNoReturn("wrong size"); fi;
> od;

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("gh-00016.tst");
