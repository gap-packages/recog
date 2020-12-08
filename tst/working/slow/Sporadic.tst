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
gap> TestSporadic("J4"); # slow
[ "J4" ]
gap> TestSporadic("Th"); # slow
[ "Th" ]
gap> TestSporadic("Fi24'"); # slow
[ "Fi24'" ]
