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
>     if not IsLeaf(ri) then r := RIFac(ri); fi;
>     stamp := r!.fhmethsel.successMethod;
>     if stamp="ProjDeterminant" then
>         r := RIKer(r);
>         stamp := r!.fhmethsel.successMethod;
>     fi;
>     Print("Stamp: ",stamp,"\n");
>     return ri;
> end;;

#
gap> TestRecogGL(2,2);;
Stamp: ClassicalNatural
gap> TestRecogGL(3,2);;
Stamp: ClassicalNatural
gap> TestRecogGL(4,2);;
Stamp: ClassicalNatural
gap> TestRecogGL(5,2);;
Stamp: ClassicalNatural
gap> TestRecogGL(10,2);;
Stamp: ClassicalNatural

#
gap> TestRecogGL(2,3);;
Stamp: ClassicalNatural
gap> TestRecogGL(3,3);;
Stamp: ClassicalNatural
gap> TestRecogGL(4,3);;
Stamp: ClassicalNatural
gap> TestRecogGL(5,3);;
Stamp: ClassicalNatural
gap> TestRecogGL(6,3);;
Stamp: ClassicalNatural
gap> TestRecogGL(7,3);;
Stamp: ClassicalNatural
gap> TestRecogGL(8,3);;
Stamp: ClassicalNatural
gap> TestRecogGL(9,3);;
Stamp: ClassicalNatural

#
gap> TestRecogGL(2,4);;
Stamp: ClassicalNatural
gap> TestRecogGL(3,4);;
Stamp: ClassicalNatural
gap> TestRecogGL(4,4);;
Stamp: ClassicalNatural
gap> TestRecogGL(5,4);;
Stamp: ClassicalNatural
gap> TestRecogGL(6,4);;
Stamp: ClassicalNatural

#
gap> TestRecogGL(2,5);;
Stamp: ClassicalNatural
gap> TestRecogGL(3,5);;
Stamp: ClassicalNatural
gap> TestRecogGL(4,5);;
Stamp: ClassicalNatural
gap> TestRecogGL(5,5);;
Stamp: ClassicalNatural
gap> TestRecogGL(6,5);;
Stamp: ClassicalNatural

#
gap> TestRecogGL(3,8);;
Stamp: ClassicalNatural
gap> TestRecogGL(4,8);;
Stamp: ClassicalNatural
gap> TestRecogGL(5,8);;
Stamp: ClassicalNatural

#
gap> TestRecogGL(2,9);;
Stamp: ClassicalNatural
gap> TestRecogGL(3,9);;
Stamp: ClassicalNatural

#
gap> TestRecogGL(3,16);;
Stamp: ClassicalNatural
gap> TestRecogGL(4,16);;
Stamp: ClassicalNatural

#
gap> TestRecogGL(2,25);;
Stamp: ClassicalNatural
gap> TestRecogGL(3,25);;
Stamp: ClassicalNatural
gap> TestRecogGL(4,25);;
Stamp: ClassicalNatural

#
gap> TestRecogGL(2,27);;
Stamp: ClassicalNatural
gap> TestRecogGL(3,27);;
Stamp: ClassicalNatural
gap> TestRecogGL(4,27);;
Stamp: ClassicalNatural
