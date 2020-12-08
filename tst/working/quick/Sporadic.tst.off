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
gap> TestSporadic("J1");
[ "J1" ]
gap> TestSporadic("M11");
[ "M11" ]
gap> TestSporadic("J3");
[ "J3" ]
gap> TestSporadic("M23");
[ "M23" ]
gap> TestSporadic("M22");
[ "M22" ]
gap> TestSporadic("J2");
[ "J2" ]
gap> TestSporadic("Ru");
[ "Ru" ]
gap> TestSporadic("HS");
[ "HS" ]
gap> TestSporadic("M24");
[ "M24" ]
gap> TestSporadic("ON");
[ "ON" ]
gap> TestSporadic("McL");
[ "McL" ]
gap> TestSporadic("Co3");
[ "Co3" ]
gap> TestSporadic("Co2");
[ "Co2" ]
gap> TestSporadic("Suz");
[ "Suz" ]
gap> TestSporadic("Fi23");
[ "Fi23" ]
gap> TestSporadic("M12");
[ "M12" ]
gap> TestSporadic("Fi22");
[ "Fi22" ]
gap> TestSporadic("Co1");
[ "Co1" ]
gap> TestSporadic("He");
[ "He" ]
