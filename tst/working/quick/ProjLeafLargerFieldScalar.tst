gap> START_TEST("ProjLeafLargerFieldScalar.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);

# A projective element may reach a PSL leaf multiplied by a scalar from a
# larger field than that of the leaf, for example through BlocksModScalars.
gap> TestScaled := function(G, lambda)
>   local ri, g, slp;
>   ri := RecogniseProjectiveGroup(G);
>   g := PseudoRandom(G);
>   slp := SLPforElement(ri, lambda * g);
>   return slp <> fail and
>     IsEqualProjective(ResultOfStraightLineProgram(slp, NiceGens(ri)), g);
> end;;

# PSL2 leaf; the square of Z(25)^3 is a non-square of GF(5)
gap> TestScaled(SL(2,5), Z(25));
true
gap> TestScaled(SL(2,5), Z(25)^3);
true

# PSLd leaf
gap> TestScaled(SL(4,11), Z(121));
true

# an element that is no scalar multiple of a matrix over the field of the leaf
gap> ri := RecogniseProjectiveGroup(SL(2,5));;
gap> SLPforElement(ri, [[Z(25), 0*Z(5)], [0*Z(5), Z(5)^0]]);
fail
gap> ri := RecogniseProjectiveGroup(SL(4,11));;
gap> SLPforElement(ri, DiagonalMat([Z(121), Z(11)^0, Z(11)^0, Z(11)^0]));
fail

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("ProjLeafLargerFieldScalar.tst");
