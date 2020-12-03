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
gap> d:=3;; for q in [2, 3, 4, 5, 7, 8, 9, 11, 13] do TestNaming("SL", d, q); od;
gap> d:=4;; for q in [2, 3, 4, 5, 7, 8, 9, 11, 13] do TestNaming("SL", d, q); od;
gap> d:=5;; for q in [2, 3, 4, 5, 7, 8, 9, 11, 13] do TestNaming("SL", d, q); od;

#
# orthogonal groups, odd dimension
#
# FIXME/TODO: SO(3,9) has bad value for isSOContained; expected true, got unknown
# FIXME/TODO: sometimes get SO(3,11) has bad value for isSOContained; expected true, got unknown
# FIXME/TODO: sometimes get SO(5,3) has bad value for isSOContained; expected true, got unknown
# FIXME/TODO: sometimes get SO(7,3) has bad value for isSOContained; expected true, got unknown
gap> d:=3;; for q in [2, 3, 4, 5, 7, 8, 13] do TestNaming("SO", d, q); od;
gap> d:=5;; for q in [2, 4, 5, 7, 8, 9, 11, 13] do TestNaming("SO", d, q); od;
gap> d:=7;; for q in [2, 4, 5, 7, 8, 9, 11, 13] do TestNaming("SO", d, q); od;

# orthogonal groups, even dimension, plus form
# O^+(4,q) with q = 8 or q >= 11 are non-generic
# FIXME/TODO: non-generic sometimes are not recognized correctly
# FIXME/TODO: sometimes get SO(1,8,4) has bad value for isSOContained; expected true, got unknown
gap> d:=4;; for q in [2, 3, 4, 5, 7, 9] do TestNaming("SO", +1, d, q); od;
gap> d:=6;; for q in [2, 3, 4, 5, 7, 8, 9, 11, 13] do TestNaming("SO", +1, d, q); od;
gap> d:=8;; for q in [2, 3, 5, 7, 8, 9, 11, 13] do TestNaming("SO", +1, d, q); od;

#
# orthogonal groups, even dimension, minus form
#
# FIXME/TODO: sometimes get SO(-1,6,2) has bad value for isSOContained; expected true, got unknown
# FIXME/TODO: sometimes get SO(-1,6,3) has bad value for isSOContained; expected true, got unknown
gap> d:=4;; for q in [2, 3, 4, 5, 7, 8, 9, 11, 13] do TestNaming("SO", -1, d, q); od;
gap> d:=6;; for q in [4, 5, 7, 8, 9, 11, 13] do TestNaming("SO", -1, d, q); od;
gap> d:=8;; for q in [2, 3, 4, 5, 7, 8, 9, 11, 13] do TestNaming("SO", -1, d, q); od;

#
# symplectic groups
#
# Note: Sp(2n, 2^f) \cong SO(2n+1, 2^f)
# FIXME/TODO: always get Sp(4,4) has bad value for isSpContained; expected true, got unknown
# FIXME/TODO: sometimes get Sp(4,9) has bad value for isSpContained; expected true, got unknown
# FIXME/TODO: sometimes get Sp(4,13) has bad value for isSpContained; expected true, got unknown
# FIXME/TODO: sometimes get Sp(6,2) has bad value for isSpContained; expected true, got unknown
gap> d:=4;; for q in [2, 3, 5, 7, 8, 11] do TestNaming("Sp", d, q); od;
gap> d:=6;; for q in [3, 4, 5, 7, 8, 9, 11, 13] do TestNaming("Sp", d, q); od;
gap> d:=8;; for q in [2, 3, 4, 5, 7, 8, 9, 11, 13] do TestNaming("Sp", d, q); od;

#
# unitary groups
#
# TODO: the non-generic codes are also recognized as symplectic? see code dealing
# with that inside 'TestNaming'
# FIXME/TODO: sometimes get SU(6,2) has bad value for isSUContained; expected true, got unknown
gap> d:=3;; for q in [2, 3, 4, 5, 7, 8, 9, 11, 13] do TestNaming("SU", d, q); od;
gap> d:=4;; for q in [2, 3, 4, 5, 7, 8, 9, 11, 13] do TestNaming("SU", d, q); od;
gap> d:=5;; for q in [2, 3, 4, 5, 7, 8, 9, 11, 13] do TestNaming("SU", d, q); od;
gap> d:=6;; for q in [3, 4, 5, 7, 8, 9, 11, 13] do TestNaming("SU", d, q); od;
