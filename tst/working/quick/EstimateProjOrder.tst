gap> START_TEST("EstimateProjOrder.tst");

# The estimate must divide the projective order: NonGenericOrthogonalPlus
# rejects O+(4,q) when it is not a multiple of |POmega(+1,4,q)|. For this
# seed, the second basic orbit of the genss chain is not closed under the
# generators of the third layer; the product of the orbit lengths was 230400.
gap> G := SO(+1, 4, 9);;
gap> Reset(GlobalMersenneTwister, 430);; Reset(GlobalRandomSource, 430);;
gap> RECOG.EstimateProjOrder(Group(GeneratorsOfGroup(G)));
259200

#
gap> STOP_TEST("EstimateProjOrder.tst");
