#
# This file contains tests for the naming (= non-constructive recognition) of
# classical groups as implemented in classical.gi; see also [NP97], [NP98]
#
gap> ReadPackage("recog", "tst/naming.g");
true

#
# linear groups
#
#@if not IsBound(RECOG_TEST_SUITE) or RECOG_TEST_SUITE = "quick"
gap> d:=3;; for q in [2, 3] do TestNaming("SL", d, q); od;
#@fi
#@if not IsBound(RECOG_TEST_SUITE) or RECOG_TEST_SUITE = "slow"
gap> d:=3;; for q in [4, 5, 7, 8, 9, 11, 13] do TestNaming("SL", d, q); od;
gap> d:=4;; for q in [2, 3, 4, 5, 7, 8, 9, 11, 13] do TestNaming("SL", d, q); od;
gap> d:=5;; for q in [2, 3, 4, 5, 7, 8, 9, 11, 13] do TestNaming("SL", d, q); od;
#@fi

#
# orthogonal groups, odd dimension
#
#@if not IsBound(RECOG_TEST_SUITE) or RECOG_TEST_SUITE = "quick"
gap> d:=3;; for q in [2, 3] do TestNaming("SO", d, q); od;
#@fi

#@if not IsBound(RECOG_TEST_SUITE) or RECOG_TEST_SUITE = "slow"
gap> d:=3;; for q in [2, 3, 4, 5, 7, 8, 9, 11, 13] do TestNaming("SO", d, q); od;
gap> d:=5;; for q in [2, 3, 4, 5, 7, 8, 9, 11, 13] do TestNaming("SO", d, q); od;
gap> d:=7;; for q in [2, 3, 4, 5, 7, 8, 9, 11, 13] do TestNaming("SO", d, q); od;
#@fi

#
# orthogonal groups, even dimension, plus form
#
# O^+(4,q) with q = 8 or q >= 11 are non-generic
#
#@if not IsBound(RECOG_TEST_SUITE) or RECOG_TEST_SUITE = "quick"
gap> d:=4;; for q in [2, 3] do TestNaming("SO", +1, d, q); od;
#@fi

#@if not IsBound(RECOG_TEST_SUITE) or RECOG_TEST_SUITE = "slow"
gap> d:=4;; for q in [2, 3, 4, 5, 7, 8, 9, 11, 13] do TestNaming("SO", +1, d, q); od;
gap> d:=6;; for q in [2, 3, 4, 5, 7, 8, 9, 11, 13] do TestNaming("SO", +1, d, q); od;
gap> d:=8;; for q in [2, 3, 4, 5, 7, 8, 9, 11, 13] do TestNaming("SO", +1, d, q); od;
gap> d:=10;; for q in [2, 3, 4, 5] do TestNaming("SO", +1, d, q); od;
gap> d:=12;; for q in [2, 3, 4, 5] do TestNaming("SO", +1, d, q); od;
#@fi

#
# orthogonal groups, even dimension, minus form
#
#@if not IsBound(RECOG_TEST_SUITE) or RECOG_TEST_SUITE = "quick"
gap> d:=4;; for q in [2, 3] do TestNaming("SO", -1, d, q); od;
#@fi

#@if not IsBound(RECOG_TEST_SUITE) or RECOG_TEST_SUITE = "slow"
gap> d:=4;; for q in [2, 3, 4, 5, 7, 8, 9, 11, 13] do TestNaming("SO", -1, d, q); od;
gap> d:=6;; for q in [2, 3, 4, 5, 7, 8, 9, 11, 13] do TestNaming("SO", -1, d, q); od;
gap> d:=8;; for q in [2, 3, 4, 5, 7, 8, 9, 11, 13] do TestNaming("SO", -1, d, q); od;
#@fi

#
# symplectic groups
#
# Note: Sp(2n, 2^f) \cong SO(2n+1, 2^f)
#@if not IsBound(RECOG_TEST_SUITE) or RECOG_TEST_SUITE = "quick"
gap> d:=4;; for q in [2, 3] do TestNaming("Sp", d, q); od;
#@fi

#@if not IsBound(RECOG_TEST_SUITE) or RECOG_TEST_SUITE = "slow"
gap> d:=4;; for q in [2, 3, 4, 5, 7, 8, 9, 11, 13] do TestNaming("Sp", d, q); od;
gap> d:=6;; for q in [2, 3, 4, 5, 7, 8, 9, 11, 13] do TestNaming("Sp", d, q); od;
gap> d:=8;; for q in [2, 3, 4, 5, 7, 8, 9, 11, 13] do TestNaming("Sp", d, q); od;
#@fi

#
# unitary groups
#
#@if not IsBound(RECOG_TEST_SUITE) or RECOG_TEST_SUITE = "quick"
gap> d:=3;; for q in [2, 3] do TestNaming("SU", d, q); od;
#@fi

#@if not IsBound(RECOG_TEST_SUITE) or RECOG_TEST_SUITE = "slow"
gap> d:=3;; for q in [2, 3, 4, 5, 7, 8, 9, 11, 13] do TestNaming("SU", d, q); od;
gap> d:=4;; for q in [2, 3, 4, 5, 7, 8, 9, 11, 13] do TestNaming("SU", d, q); od;
gap> d:=5;; for q in [2, 3, 4, 5, 7, 8, 9, 11, 13] do TestNaming("SU", d, q); od;
gap> d:=6;; for q in [2, 3, 4, 5, 7, 8, 9, 11, 13] do TestNaming("SU", d, q); od;
#@fi
