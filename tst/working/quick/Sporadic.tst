# test recognition of sporadic groups
# TODO: right now, we only test the first representation stored in AtlasRep;
# ideally, we should test more
gap> TestSporadic := function(name)
>     local g, ri;
>     g := AtlasGenerators(name,1).generators;
>     g := Group(g);
>     ri := EmptyRecognitionInfoRecord(rec(),g,IsMatrixGroup(g));
>     return FindHomMethodsProjective.NameSporadic(ri, g : DEBUGRECOGSPORADICS);
> end;;

#
gap> data := ShallowCopy(RECOG.NameSporadicData);;

# We test everything from RECOG.NameSporadicData except for "HN" and "Ly"
# because they take very long.
# "HN" is not in RECOG.NameSporadicData. We remove "Ly".
gap> Remove(data, PositionProperty(data, x -> x.name = "Ly"));;
gap> for d in data do
> name := d.name;
> Print(name, "\n");
> TestSporadic(name);
> od;
M11
M12
M22
M23
M24
J1
J2
J3
HS
McL
Suz
Ru
Co3
Co2
Co1
ON
Fi22
He
J4
Fi23
Fi24'
Th
