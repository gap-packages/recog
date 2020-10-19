# test recognition of sporadic groups
# TODO: right now, we only test the first representation stored in AtlasRep;
# ideally, we should test more
gap> TestSporadic := function(name)
>     local g, ri;
>     g := AtlasGenerators(name,1).generators;
>     g := Group(g);
>     ri := EmptyRecognitionInfoRecord(rec(),g,IsMatrixGroup(g));
>     return FindHomMethodsProjective.SporadicsByOrders(ri,g:DEBUGRECOGSPORADICS);
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
gap> TestSporadic("J4");
[ "J4" ]
gap> TestSporadic("ON");
[ "ON" ]
gap> TestSporadic("Th");
[ "Th" ]
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
gap> TestSporadic("M12.2");
[ "M12.2" ]
gap> TestSporadic("M22.2");
[ "M22.2" ]
gap> TestSporadic("J2.2");
[ "J2.2" ]
gap> TestSporadic("McL.2");
[ "McL.2" ]
gap> TestSporadic("Suz.2");
[ "Suz.2" ]
gap> TestSporadic("Fi22.2");
[ "Fi22.2" ]
gap> TestSporadic("J3.2");
[ "J3.2" ]
gap> TestSporadic("2F4(2)'");
[ "2F4(2)'" ]
