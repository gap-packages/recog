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

# The group in which this was found, of order 576 in GL(4,4): a diagonal
# block generates GL(2,2), and the last generator is not scalar on it
gap> one := IdentityMat(4, GF(4));;
gap> Elementary := function(i, j)
>   local m;
>   m := NullMat(4, 4, GF(4));
>   m[i,j] := Z(2);
>   return m;
> end;;
gap> gens := [one, one + Elementary(2,3), PermutationMat((2,3), 4, GF(4)),
>             one + Elementary(4,1), one + Elementary(2,1) + Elementary(4,3),
>             DiagonalMat([Z(4), Z(4)^2, Z(4)^2, Z(4)])];;
gap> Reset(GlobalMersenneTwister, 1);; Reset(GlobalRandomSource, 1);;
gap> ri := RecogniseGroup(GroupWithGenerators(gens));;
gap> IsReady(ri) and Size(ri) = 576;
true

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("ProjLeafLargerFieldScalar.tst");
