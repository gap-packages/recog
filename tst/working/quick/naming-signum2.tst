#
gap> START_TEST("naming-signum2.tst");

# A plane with Q(e) = a, Q(f) = b, B(e,f) = 1 is hyperbolic over GF(q)
# iff x^2 + x + ab has a root in GF(q), also if a, b lie in a subfield
gap> Sgn := {q, a, b} -> RECOG.Signum2(GF(q), [[0, 1], [1, 0]] * Z(q)^0,
>                                      [[a, 1], [0, b]] * Z(q)^0);;
gap> List([[4, 1, 1], [16, 1, 1], [16, 1, Z(4)], [4, 1, Z(4)], [8, 1, 1]],
>         x -> CallFuncList(Sgn, x));
[ 1, 1, 1, -1, -1 ]

# hence Omega^-(4,q) and Omega^+(6,q) are named for q = 4, 16
gap> ForAll([4, 16], q -> ForAll([1 .. 20], i ->
>        RecogniseClassical(Omega(-1, 4, q)^RandomInvertibleMat(4, GF(q)))
>        .isOmegaContained = true));
true
gap> ForAll([1 .. 20], i ->
>        RecogniseClassical(Omega(1, 6, 4)^RandomInvertibleMat(6, GF(4)))
>        .isOmegaContained = true);
true

#
gap> STOP_TEST("naming-signum2.tst");
