#@local S19OnSets, jellyGroup, n, random, jellyGroupConj, ri

# Test for LargeBasePrimitive
gap> S19OnSets := Action(SymmetricGroup(19), Combinations([1 .. 19], 2), OnSets);;
gap> jellyGroup := WreathProductProductAction(S19OnSets, Group((1,2)));;
gap> n := NrMovedPoints(jellyGroup);;
gap> # Take a random conjugate
gap> random := Random(SymmetricGroup(n));;
gap> jellyGroupConj := jellyGroup ^ random;;
gap> RECOG.TestGroup(jellyGroupConj,
>   false,
>   Size(jellyGroup),
>   rec(tryNonGroupElements := true));;
