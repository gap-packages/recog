#
gap> TestRecogGL := function(d,q)
>     local h, gens, g, ri, r, stamp;
>     h := GL(d,q);
>     gens := List([1..10],x->PseudoRandom(h));
>     # FIXME: while this is a generating set with HIGH PROBABILITY, it is not always one.
>     # This could lead to spurious failures in the test suite...
>     g := GroupWithGenerators(gens);
>     ri := RECOG.TestGroup(g,false,Size(h));
>     r := ri;
>     if not(IsLeaf(ri)) then r := RIFac(ri); fi;
>     stamp := r!.fhmethsel.successMethod;
>     if stamp="ProjDeterminant" then
>         r := RIKer(r);
>         stamp := r!.fhmethsel.successMethod;
>     fi;
>     Print("Stamp: ",stamp,"\n");
>     return ri;
> end;;


gap> TestRecogGL(9,5);; # FIXME buggy, see issue #37
gap> TestRecogGL(2,8);; # FIXME: see issue #12
gap> TestRecogGL(2,16);; # FIXME: see issue #12
gap> TestRecogGL(8,27);; # FIXME: see issue #12
