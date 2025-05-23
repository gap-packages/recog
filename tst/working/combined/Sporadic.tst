# test recognition of sporadic groups
# TODO: right now, we only test the first representation stored in AtlasRep;
# ideally, we should test more
gap> TestSporadic := function(name)
>     local g, ri;
>     g := AtlasGenerators(name,1).generators;
>     g := Group(g);
>     ri := RecogNode(g,IsMatrixGroup(g));
>     return FindHomMethodsProjective.NameSporadic(ri, g : DEBUGRECOGSPORADICS);
> end;;

#
gap> data := Set(RECOG.NameSporadicData, x -> x.name);;

# We don't test "HN" and "Ly" at all because they take very long.
# "HN" is not in RECOG.NameSporadicData. We remove "Ly".
gap> RemoveSet(data, "Ly");

# Groups handled by the "quick" or the "veryslow" suite.
gap> quick := ["M23", "Suz", "Fi23"];;
gap> veryslow := ["J4", "Th", "Fi24'"];;

#@if not IsBound(RECOG_TEST_SUITE) or RECOG_TEST_SUITE = "quick"
gap> for name in quick do
> Print(name, "\n");
> TestSporadic(name);
> od;
M23
Suz
Fi23
#@fi
#@if not IsBound(RECOG_TEST_SUITE) or RECOG_TEST_SUITE = "veryslow"
gap> for name in veryslow do
> Print(name, "\n");
> TestSporadic(name);
> od;
J4
Th
Fi24'
#@fi
#@if not IsBound(RECOG_TEST_SUITE) or RECOG_TEST_SUITE = "slow"
gap> SubtractSet(data, quick);
gap> SubtractSet(data, veryslow);
gap> for name in data do
> Print(name, "\n");
> TestSporadic(name);
> od;
Co1
Co2
Co3
Fi22
HS
He
J1
J2
J3
M11
M12
M22
M24
McL
ON
Ru
#@fi
