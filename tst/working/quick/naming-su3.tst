#
gap> START_TEST("naming-su3.tst");

# SU(3,3) needs an element of projective order divisible by 6 whose power of
# projective order 2 is not central. With the scalar Z(9) of order 8, an
# element h of order 6 becomes g = h*Z(9) of order 24, and g^12 = -1 is central
gap> G := Group(Concatenation(GeneratorsOfGroup(SU(3, 3)),
>                             [Z(9) * IdentityMat(3, GF(9))]));;
gap> ForAll([1 .. 300], i -> RecogniseClassical(G).isSUContained = true);
true

#
gap> STOP_TEST("naming-su3.tst");
