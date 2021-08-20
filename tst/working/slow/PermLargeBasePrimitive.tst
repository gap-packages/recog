#@local S17OnSets, jellyGroup, n, random, jellyGroupConj, ri
#@local addFixedPointsPerm, jellyGroupWithFixedPoints, riWithFixed

# Test for LargeBasePrimitive
gap> S17OnSets := Action(SymmetricGroup(17), Combinations([1 .. 17], 2), OnSets);;
gap> jellyGroup := WreathProductProductAction(S17OnSets, Group((1,2)));;
gap> n := NrMovedPoints(jellyGroup);;
gap> # Take a random conjugate
gap> random := Random(SymmetricGroup(n));;
gap> jellyGroupConj := jellyGroup ^ random;;
gap> ri := RECOG.TestGroup(jellyGroupConj,
>   false,
>   Size(jellyGroup),
>   rec(tryNonGroupElements := true));;
gap> ri!.fhmethsel.successMethod;
"LargeBasePrimitive"

# Test that groups with fixed points are handled together by
# ThrowAwayFixedPoints and LargeBasePrimitive, confer:
# https://github.com/gap-packages/recog/issues/190
# https://github.com/gap-packages/recog/pull/191
gap> addFixedPointsPerm := Random(SymmetricGroup(5 * QuoInt(n,2)));;
gap> jellyGroupWithFixedPoints := jellyGroup ^ addFixedPointsPerm;;
gap> riWithFixed := RECOG.TestGroup(jellyGroupWithFixedPoints,
>   false,
>   Size(jellyGroup),
>   rec(tryNonGroupElements := true));;
gap> riWithFixed!.fhmethsel.successMethod;
"ThrowAwayFixedPoints"
gap> ImageRecogNode(riWithFixed)!.fhmethsel.successMethod;
"LargeBasePrimitive"
