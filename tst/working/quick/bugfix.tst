#
gap> START_TEST("bugfix.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);

# See https://github.com/gap-packages/recog/issues/1
gap> gens := [];; e:=Z(2)^0;;
gap> mat:=IdentityMat(4,GF(2));; mat[1,2]:=e;; Add(gens, mat);
gap> mat:=IdentityMat(4,GF(2));; mat[2,1]:=e;; Add(gens, mat);
gap> mat:=IdentityMat(4,GF(2));; mat[3,2]:=e;; Add(gens, mat);
gap> mat:=IdentityMat(4,GF(2));; mat[4,3]:=e;; Add(gens, mat);
gap> G:=Group(gens);
<matrix group with 4 generators>
gap> ri:=RECOG.TestGroup(G, false, 192);;
gap> outsider:=Reversed(IdentityMat(4,GF(2)));;
gap> outsider in ri;
false

# Issue #16
gap> g := DirectProduct(SymmetricGroup(12),SymmetricGroup(5));;
gap> for i in [1..30] do
>   h:=g^Random(SymmetricGroup(37));
>   r:=RecogniseGroup(h);
>   if Size(r) <> Size(g) then ErrorNoReturn("wrong size"); fi;
> od;

# verify issue #38 is resolved
gap> RECOG.TestGroup(SymmetricGroup(11), false, Factorial(11));
<recognition node Giant AlmostSimple Size=39916800>

# See https://github.com/gap-packages/recog/issues/65
gap> RecogniseGroup(SL(2,2));
<recognition node GoProjective Dim=2 Field=2
 F:<recognition node (projective) ClassicalNatural Comment=PSL2Even Size=
6 Dim=2 Field=2>
 K:<trivial kernel>
gap> RecogniseGroup(SL(2,3));
<recognition node GoProjective Dim=2 Field=3
 F:<recognition node (projective) ClassicalNatural Comment=PSL2Odd Size=
12 Dim=2 Field=3>
 K:<recognition node DiagonalMatrices Dim=2 Field=3
    F:<recognition node Scalar Dim=1 Field=3>
    K:<trivial kernel>>
gap> RecogniseGroup(SL(2,4));
<recognition node GoProjective Dim=2 Field=4
 F:<recognition node (projective) ClassicalNatural Comment=PSL2Even Simple Siz\
e=60 Dim=2 Field=4>
 K:<trivial kernel>
gap> RecogniseGroup(SL(2,5));
<recognition node GoProjective Dim=2 Field=5
 F:<recognition node (projective) ClassicalNatural Comment=PSL2Odd Simple Size\
=60 Dim=2 Field=5>
 K:<recognition node DiagonalMatrices Dim=2 Field=5
    F:<recognition node Scalar Dim=1 Field=5>
    K:<trivial kernel>>

# We had a bug where RECOG.IsScalarMat was used incorrectly (return value was
# assumed to be true or false, but could be an FFE). This example used to
# trigger the error, which looked like this:
#   Error, <expr> must be 'true' or 'false' (not an ffe)
gap> RECOG.IsThisSL2Natural(rec(), [ [ [ 0*Z(5), Z(5^2)^9 ], [ Z(5^2)^3, 0*Z(5) ] ], [ [ Z(5), 0*Z(5) ], [ 0*Z(5), Z(5)^3 ] ] ], GF(5^2));
false

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("bugfix.tst");
