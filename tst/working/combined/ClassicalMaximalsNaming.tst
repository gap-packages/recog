#
# RecogniseClassical must not name a maximal subgroup of a classical group as
# the full group; see TestNamingMaximals in tst/naming.g. The subgroups come
# from the ClassicalMaximals package, which first shipped with GAP 4.16.
#
#@if TestPackageAvailability("ClassicalMaximals") <> fail
gap> LoadPackage("ClassicalMaximals", false);
true
gap> oldCMInfoLevel := InfoLevel(InfoClassicalMaximals);;
gap> oldOrbInfoLevel := InfoLevel(InfoOrb);;
gap> SetInfoLevel(InfoClassicalMaximals, 0);
gap> SetInfoLevel(InfoOrb, 0);
gap> ReadPackage("recog", "tst/naming.g");
true
#@fi

#@if TestPackageAvailability("ClassicalMaximals") <> fail and (not IsBound(RECOG_TEST_SUITE) or RECOG_TEST_SUITE = "quick")
gap> d:=3;; for q in [2, 3, 4, 5] do TestNamingMaximals("L", d, q); od;
gap> d:=3;; for q in [3] do TestNamingMaximals("U", d, q); od;
gap> d:=4;; for q in [4] do TestNamingMaximals("S", d, q); od;
gap> d:=5;; for q in [3] do TestNamingMaximals("O", d, q); od;
gap> d:=6;; for q in [2] do TestNamingMaximals("O+", d, q); od;
gap> d:=4;; for q in [3] do TestNamingMaximals("O-", d, q); od;
#@fi

#@if TestPackageAvailability("ClassicalMaximals") <> fail and (not IsBound(RECOG_TEST_SUITE) or RECOG_TEST_SUITE = "slow")
gap> d:=3;; for q in [7, 8, 9, 11, 13] do TestNamingMaximals("L", d, q); od;
gap> d:=4;; for q in [2, 3, 4, 5, 7, 8, 9] do TestNamingMaximals("L", d, q); od;
gap> d:=5;; for q in [2, 3, 4, 5, 7, 8, 9] do TestNamingMaximals("L", d, q); od;
gap> d:=6;; for q in [2, 3, 4, 5] do TestNamingMaximals("L", d, q); od;
gap> d:=3;; for q in [4, 5, 7, 8, 9] do TestNamingMaximals("U", d, q); od;
gap> d:=4;; for q in [2, 3, 4, 8] do TestNamingMaximals("U", d, q); od;
gap> d:=5;; for q in [2, 3, 4] do TestNamingMaximals("U", d, q); od;
gap> d:=6;; for q in [2, 4] do TestNamingMaximals("U", d, q); od;
gap> d:=4;; for q in [5, 8] do TestNamingMaximals("S", d, q); od;
gap> d:=6;; for q in [2, 3, 4, 5, 8] do TestNamingMaximals("S", d, q); od;
gap> d:=8;; for q in [2, 4] do TestNamingMaximals("S", d, q); od;
gap> d:=5;; for q in [5, 7, 9] do TestNamingMaximals("O", d, q); od;
gap> d:=7;; for q in [3, 5, 7, 9] do TestNamingMaximals("O", d, q); od;
gap> d:=6;; for q in [3, 4, 5, 8] do TestNamingMaximals("O+", d, q); od;
gap> d:=8;; for q in [2] do TestNamingMaximals("O+", d, q); od;

# For q = 3, 5 only the subgroups of order |SO(7,q)|, among them Spin(7,q),
# which the 4-form test must reject; the full sweep takes about a minute.
gap> d:=8;; for q in [3, 5] do
>      TestNamingMaximals("O+", d, q, M -> Size(M) = Size(SO(d - 1, q)));
>    od;
gap> d:=4;; for q in [2, 4, 5, 7, 9] do TestNamingMaximals("O-", d, q); od;
gap> d:=6;; for q in [2, 4, 5] do TestNamingMaximals("O-", d, q); od;
gap> d:=8;; for q in [3] do TestNamingMaximals("O-", d, q); od;
#@fi

#@if TestPackageAvailability("ClassicalMaximals") <> fail
gap> SetInfoLevel(InfoClassicalMaximals, oldCMInfoLevel);
gap> SetInfoLevel(InfoOrb, oldOrbInfoLevel);
#@fi
