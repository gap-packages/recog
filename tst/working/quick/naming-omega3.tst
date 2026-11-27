#
gap> START_TEST("naming-omega3.tst");

# Omega(3,29) has q+1 = 2*3*5: its elements of order 15 are large ppd
# elements because of the prime 5
gap> ForAll([1 .. 5], i -> RecogniseClassical(Omega(3, 29)).isOmegaContained
>                          = true);
true

# A5 is an irreducible subgroup of Omega(3,q) for q = +-1 mod 10. Scalars
# raise its element orders above 5, the projective orders stay at most 5.
gap> A5WithScalar := function(q, scalar)
>     local O, H;
>     O := Omega(3, q);
>     H := First(List(ConjugacyClassesMaximalSubgroups(O), Representative),
>                H -> Size(H) = 60);
>     return Group(Concatenation(GeneratorsOfGroup(H), [scalar * One(O)]));
> end;;
gap> ForAny([[29, Z(29)], [49, -Z(7)^0], [49, Z(49)], [79, -Z(79)^0]],
>         c -> RecogniseClassical(A5WithScalar(c[1], c[2])).isOmegaContained
>              = true);
false

# Omega(3,q) with scalars is still named
gap> ForAll([29, 49, 79], q -> RecogniseClassical(Group(Concatenation(
>         GeneratorsOfGroup(Omega(3, q)), [Z(q) * IdentityMat(3, GF(q))])))
>         .isOmegaContained = true);
true

# For q = 9 the test wants an element of projective order 4. An involution
# times a scalar of order 4 or 8 has matrix order 4 or 8 and a central square.
gap> G := Group(Concatenation(GeneratorsOfGroup(Omega(3, 9)),
>                             [Z(9) * IdentityMat(3, GF(9))]));;
gap> ForAny([1 .. 30], i -> RecogniseClassical(G).isOmegaContained = false);
false
gap> ForAny([Z(9), Z(9)^2], z ->
>         RecogniseClassical(A5WithScalar(9, z)).isOmegaContained = true);
false

#
gap> STOP_TEST("naming-omega3.tst");
