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

#
gap> STOP_TEST("ProjC6Core.tst");
