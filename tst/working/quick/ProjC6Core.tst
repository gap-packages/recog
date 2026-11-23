gap> START_TEST("ProjC6Core.tst");

# A scalar in the generator list must not hide the generator after it.
# Here T and D form a hyperbolic pair of 3^(1+2).
gap> T := PermutationMat((1,2,3), 3, GF(7));;
gap> D := DiagonalMat([1, Z(7)^2, Z(7)^4] * Z(7)^0);;
gap> res := RECOG.basis2(3, 1, 7, GroupWithGenerators([One(T), T, D]));;
gap> res.blocks;
[  ]
gap> Length(res.basis.sympl);
2

# If the conjugates found by BlindDescent span a subspace of R/Z(R) that the
# group does not normalise, C6 must enlarge it rather than give up. A single
# element of R spans such a subspace.
gap> h := RECOG.MakeC6Group(Sp(4,3), Sp(4,3), 7);;
gap> G := h[1];;
gap> a := GeneratorsOfGroup(G)[1];;
gap> BlindDescent := RECOG.BlindDescent;;
gap> RECOG.BlindDescent := function(r, n, grp, limit)
>      return [a, [a]];
>    end;;
gap> re := RECOG.New2RecogniseC6(G);;
gap> RECOG.BlindDescent := BlindDescent;;
gap> re.basis.blocks;
[  ]
gap> Size(Group(re.igens)) = Size(Sp(4,3));
true

# Two elements with a non-scalar commutator do not lie in an extraspecial
# group modulo scalars. Here they share an eigenvector, so the eigenspaces
# of one are not permuted by the other.
gap> a := DiagonalMat([1, -1] * Z(9)^0);;
gap> b := [[1, 1], [0, -1]] * Z(9)^0;;
gap> RECOG.basis2(2, 1, 9, GroupWithGenerators([a, b]));
fail
gap> RECOG.basis2(2, 1, 9, GroupWithGenerators([-a, b]));
fail

# A scalar commutator is not enough either: here a has four eigenspaces of
# dimension 1, not two of dimension 2
gap> a := DiagonalMat([1, -1, 2, -2] * Z(5)^0);;
gap> b := PermutationMat((1,2)(3,4), 4, GF(5));;
gap> RECOG.IsScalarMat(Comm(a, b));
true
gap> RECOG.basis2(2, 2, 5, GroupWithGenerators([a, b]));
fail

# SL(2,5) o C8 in GL(2,9) is not a C6 group, but contains such pairs
gap> z := Z(9);;
gap> G := GroupWithGenerators([[[z^2, 0*z], [z^6, z^6]], [[0*z, z], [z^3, z^4]],
>         [[z^4, 0*z], [0*z, z^4]], [[z, 0*z], [0*z, z]]]);;
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);
gap> Reset(GlobalMersenneTwister, 1);; Reset(GlobalRandomSource, 1);;
gap> ri := RecogniseProjectiveGroup(G);;
gap> IsReady(ri) and Size(ri) = 60;
true
gap> SetInfoLevel(InfoRecog, oldInfoLevel);

#
gap> STOP_TEST("ProjC6Core.tst");
