#
# This file contains tests for the naming (= non-constructive recognition) of
# classical groups as implemented in classical.gi; see also [NP97], [NP97],
# [NP98]
#
gap> ReadPackage("recog", "tst/naming.g");
true

#
# linear groups
#
gap> d:=3;; for q in [2, 3] do TestNaming("SL", d, q); od;

#
# orthogonal groups, odd dimension
#
gap> d:=3;; for q in [2, 3] do TestNaming("SO", d, q); od;

#
# orthogonal groups, even dimension, plus form
#
gap> d:=4;; for q in [2, 3] do TestNaming("SO", +1, d, q); od;

#
# orthogonal groups, even dimension, minus form
#
gap> d:=4;; for q in [2, 3] do TestNaming("SO", -1, d, q); od;

#
# symplectic groups
#
# Note: Sp(2n, 2^f) \cong SO(2n+1, 2^f)
gap> d:=4;; for q in [2, 3] do TestNaming("Sp", d, q); od;

#
# unitary groups
#
gap> d:=3;; for q in [2, 3] do TestNaming("SU", d, q); od;
