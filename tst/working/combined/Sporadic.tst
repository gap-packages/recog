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
gap> data := ShallowCopy(RECOG.NameSporadicData);;

# We don't test "HN" and "Ly" at all because they take very long.
# "HN" is not in RECOG.NameSporadicData. We remove "Ly".
gap> Remove(data, PositionProperty(data, x -> x.name = "Ly"));;

# Groups handled by the "quick" or the "veryslow" suite.
gap> quick := [rec(name := "M23"), rec(name := "Suz"), rec(name := "Fi23")];;
gap> veryslow := [rec(name := "J4"), rec(name := "Th"), rec(name := "Fi24'")];;

#@if not IsBound(RECOG_TEST_SUITE) or RECOG_TEST_SUITE = "quick"
gap> for d in quick do
> name := d.name;
> Print(name, "\n");
> TestSporadic(name);
> od;
M23
Suz
Fi23
#@fi
#@if not IsBound(RECOG_TEST_SUITE) or RECOG_TEST_SUITE = "veryslow"
gap> for d in veryslow do
> name := d.name;
> Print(name, "\n");
> TestSporadic(name);
> od;
J4
Th
Fi24'
#@fi
#@if not IsBound(RECOG_TEST_SUITE) or RECOG_TEST_SUITE = "slow"
gap> for r in Concatenation(quick, veryslow) do
> Remove(data, PositionProperty(data, x -> x.name = r.name));;
> od;
gap> for d in data do
> name := d.name;
> Print(name, "\n");
> TestSporadic(name);
> od;
M11
M12
M22
M24
J1
J2
J3
HS
McL
Ru
Co3
Co2
Co1
ON
Fi22
He
#@fi
