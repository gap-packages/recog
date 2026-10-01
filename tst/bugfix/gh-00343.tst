gap> START_TEST("gh-00343.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);

# Issue #343: extracting a strict lower block diagonal from an immutable
# identity matrix over GF(2) must not create phantom ones.
gap> blocks := [ [ 1 .. 11 ], [ 12 .. 22 ], [ 23 .. 33 ], [ 34 .. 44 ],
>   [ 45 .. 55 ], [ 56 .. 66 ], [ 67 .. 77 ], [ 78 .. 88 ], [ 89 .. 99 ],
>   [ 100 .. 110 ], [ 111 ], [ 112 .. 121 ], [ 122 .. 132 ], [ 133 .. 143 ],
>   [ 144 .. 154 ], [ 155 .. 165 ], [ 166 .. 176 ], [ 177 .. 187 ],
>   [ 188 .. 198 ] ];;
gap> lens := [ 1946, 1815, 1694, 1573, 1452, 1331, 1210, 1100, 1089, 968,
>   957, 847, 726, 605, 484, 363, 242, 121 ];;
gap> x := IdentityMat(198, GF(2));;
gap> IsZero(RECOG.ExtractLowStuff(x, 6, blocks, lens, fail));
true

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("gh-00343.tst");
