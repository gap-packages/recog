gap> START_TEST("ProjLowIndexSubfield.tst");

# GF(23^2) has no compressed vector representation, but GAP may return a
# basis of a GF(23)-rational subspace compressed over GF(23).
# h generates a uniserial module with unique proper submodule <e1, e2>. Its
# orbit under g consists of three planes; the first two meet in <e2>, which
# g maps to <e3 + z*e4>.
gap> F := GF(23^2);; z := Z(23^2);;
gap> C := CompanionMat(MinimalPolynomial(F, Z(23^4)));;
gap> h := NullMat(4, 4, F);;
gap> h{[1, 2]}{[1, 2]} := C;; h{[3, 4]}{[3, 4]} := C;;
gap> h{[3, 4]}{[1, 2]} := IdentityMat(2, F);;
gap> A := [[1, z, 0, 0], [0, 1, 0, 0], [0, 0, 1, z], [0, 0, 0, 1]] * One(F);;
gap> g := A^-1 * PermutationMat((1, 2, 3), 4, F) * A;;
gap> res := RECOG.IndexMaxSub(GModuleByMats([h], F), Group(g), 4);;
gap> [Length(res.orb), Length(res.orb[1])];
[ 3, 1 ]

# The same for DoHintedLowIndex. G is S3 in its 2-dimensional representation;
# the elements of order 3 have the eigenlines <e1> and <e1 + z*e2>, which t
# swaps. MeatAxe picks either line at random; 21 of the seeds 1..30 picked
# <e1>.
gap> w := z^((23^2 - 1) / 3);;
gap> A := [[1, 0], [1, z]] * One(F);;
gap> x := A^-1 * DiagonalMat([w, w^2]) * A;;
gap> t := A^-1 * [[0, 1], [1, 0]] * One(F) * A;;
gap> G := Group(x, t);;
gap> hint := rec(elordersstart := [3], numberrandgens := 1, orblenlimit := 20,
>                tries := 10, triesforgens := 30);;
gap> ForAll([1 .. 10], function(seed)
>      Reset(GlobalMersenneTwister, seed);
>      Reset(GlobalRandomSource, seed);
>      return DoHintedLowIndex(RecogNode(G, true), G, hint) = Success;
>    end);
true

#
gap> STOP_TEST("ProjLowIndexSubfield.tst");
