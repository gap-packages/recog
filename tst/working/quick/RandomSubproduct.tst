gap> START_TEST("RandomSubproduct.tst");

# A trivial product is redrawn unless every entry is trivial.
gap> ForAll([1..100], i -> RandomSubproduct([(1,2)]) = (1,2));
true
gap> RandomSubproduct([(), ()]);
()
gap> RandomSubproduct(TrivialGroup(IsPermGroup));
()
gap> G := SymmetricGroup(5);;
gap> ForAll([1..100], i -> not IsOne(RandomSubproduct(G)));
true

# The identity test and the random source are options.
gap> m := [[1,1],[0,1]] * Z(5)^0;;
gap> ForAll([1..100], i -> not IsOneProjective(
>      RandomSubproduct([-One(m), m], rec(IsOne := IsOneProjective))));
true
gap> l := List([1..10], i -> Random(G));;
gap> rs := RandomSource(IsMersenneTwister, 7);;
gap> draw := {} -> List([1..10],
>      i -> RandomSubproduct(l, rec(RandomSource := rs)));;
gap> x := draw();;
gap> Reset(rs, 7);;
gap> x = draw();
true

# Argument checks.
gap> RandomSubproduct([]);
Error, <a> must be a nonempty list of group elements
gap> RandomSubproduct(1);
Error, <a> must be a group or a nonempty list of group elements
gap> RandomSubproduct(G, rec(), rec());
Error, usage: RandomSubproduct( <a>[, <opt>] )

#
gap> STOP_TEST("RandomSubproduct.tst");
