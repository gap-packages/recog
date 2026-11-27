#
gap> START_TEST("naming-d4.tst");

# Omega^+(4,q) = SL(2,q) o SL(2,q) for q = 11, 13: an element whose two
# Kronecker factors both have projective order 6 has probability 1/36
gap> ForAll([1 .. 20], i ->
>        RecogniseClassical(Omega(1, 4, 11)).isOmegaContained = true);
true
gap> ForAll([1 .. 20], i ->
>        RecogniseClassical(Omega(1, 4, 13)).isOmegaContained = true);
true

# q = 31: q+1 = 32 contains no primitive prime divisor of q^2-1
gap> ForAll([1 .. 20], i ->
>        RecogniseClassical(Omega(1, 4, 31)).isOmegaContained = true);
true

# SL(2,25) acting on the tensor product of the natural module and its Frobenius
# twist: a diagonal subgroup of Omega^+(4,25), with o1 = o2 for every element
gap> H := Group(List(GeneratorsOfGroup(SL(2, 25)),
>        g -> KroneckerProduct(g, List(g, r -> List(r, x -> x^5)))));;
gap> ForAny([1 .. 20], function(i)
>        local r;
>        r := RecogniseClassical(H);
>        return r.isOmegaContained = true and r.q = 25;
>    end);
false

# Sp(4,q) for q = 4, 9, 19: the large special ppd(4,q;2)-elements have
# proportion 1/25
gap> ForAll([4, 9, 19], q -> ForAll([1 .. 20], i ->
>        RecogniseClassical(Sp(4, q)).isSpContained = true));
true

# Sp(4,17): R = 9, so the first factor must avoid the 2 elements of order 3
gap> RECOG.Degree4WitnessProportion("symplectic", 17);
1/18
gap> ForAll([1 .. 20], i ->
>        RecogniseClassical(Sp(4, 17)).isSpContained = true);
true

# Omega^+(4,q) for q < 11, q <> 8 is named without Kronecker factor witnesses
gap> RECOG.Degree4WitnessProportion("orthogonalplus", 7);
0

#
gap> STOP_TEST("naming-d4.tst");
