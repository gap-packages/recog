gap> START_TEST("gh-00450.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);

# Issue #450: a D247 tensor witness contradicted by a tensor-factor swap
# must not raise an internal error.
# See https://github.com/gap-packages/recog/issues/450
gap> f := GF(3);;
gap> g1 := [ [ Z(3)^0, Z(3)^0 ], [ 0*Z(3), Z(3)^0 ] ];;
gap> g2 := [ [ 0*Z(3), Z(3)^0 ], [ Z(3)^0, 0*Z(3) ] ];;
gap> i2 := IdentityMat(2, f);;
gap> ngens := [ KroneckerProduct(g1, i2), KroneckerProduct(g2, i2) ];;
gap> hgens := [ KroneckerProduct(i2, g1), KroneckerProduct(i2, g2) ];;
gap> swap := [ [ Z(3)^0, 0*Z(3), 0*Z(3), 0*Z(3) ],
>   [ 0*Z(3), 0*Z(3), Z(3)^0, 0*Z(3) ],
>   [ 0*Z(3), Z(3)^0, 0*Z(3), 0*Z(3) ],
>   [ 0*Z(3), 0*Z(3), 0*Z(3), Z(3)^0 ] ];;
gap> G := Group(Concatenation(ngens, hgens, [ swap ]));;
gap> m := GModuleByMats(ngens, f);;
gap> ri := RecogNode(G, true);;
gap> RECOG.SortOutReducibleNormalSubgroup(ri, G, ngens, m);
"Success"
gap> ri!.comment;
"D7TensorInduced"
gap> Size(Image(Homom(ri)));
2

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("gh-00450.tst");
