# test recognition of sporadic groups
# TODO: right now, we only test the first representation stored in AtlasRep;
# ideally, we should test more
gap> TestSporadic := function(name)
>     local g, ri;
>     g := AtlasGenerators(name,1).generators;
>     g := Group(g);
>     ri := RecogNode(g,IsMatrixGroup(g));
>     return FindHomMethodsProjective.NameSporadic(ri);
> end;;

# NameSporadic can't recognize these groups
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
gap> TestSporadic("He.2");
[ "He.2" ]
gap> TestSporadic("Fi24'.2");
[ "Fi24'.2" ]
gap> TestSporadic("2F4(2)'.2");
[ "2F4(2)'.2" ]
gap> TestSporadic("HN.2");
[ "HN.2" ]
gap> TestSporadic("HS.2");
[ "HS.2"]
gap> TestSporadic("ON.2");
[ "ON.2" ]

gap> #TestSporadic("HN"); # FIXME: very slow
gap> #TestSporadic("Ly"); # FIXME: very slow
gap> #TestSporadic("B"); # Too big; not relevant in practice
gap> #TestSporadic("M"); # Too big; not relevant in practice
