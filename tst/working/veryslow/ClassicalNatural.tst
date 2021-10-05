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
>     if not IsLeaf(ri) then r := ImageRecogNode(ri); fi;
>     stamp := r!.fhmethsel.successMethod;
>     if stamp="ProjDeterminant" then
>         r := KernelRecogNode(r);
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
gap> TestRecogGL(6,2);;
Stamp: ClassicalNatural
gap> TestRecogGL(7,2);;
Stamp: ClassicalNatural
gap> TestRecogGL(8,2);;
Stamp: ClassicalNatural
gap> TestRecogGL(9,2);;
Stamp: ClassicalNatural
gap> TestRecogGL(10,2);;
Stamp: ClassicalNatural
gap> TestRecogGL(17,2);;
Stamp: ClassicalNatural
gap> TestRecogGL(18,2);;
Stamp: ClassicalNatural
gap> TestRecogGL(19,2);;
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
gap> TestRecogGL(17,3);;
Stamp: ClassicalNatural
gap> TestRecogGL(19,3);;
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
gap> TestRecogGL(7,4);;
Stamp: ClassicalNatural
gap> TestRecogGL(8,4);;
Stamp: ClassicalNatural
gap> TestRecogGL(9,4);;
Stamp: ClassicalNatural
gap> TestRecogGL(10,4);;
Stamp: ClassicalNatural
gap> TestRecogGL(17,4);;
Stamp: ClassicalNatural
gap> TestRecogGL(18,4);;
Stamp: ClassicalNatural
gap> TestRecogGL(19,4);;
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
gap> TestRecogGL(7,5);;
Stamp: ClassicalNatural
gap> TestRecogGL(8,5);;
Stamp: ClassicalNatural
gap> TestRecogGL(9,5);;
Stamp: ClassicalNatural
gap> TestRecogGL(10,5);;
Stamp: ClassicalNatural
gap> TestRecogGL(17,5);;
Stamp: ClassicalNatural
gap> TestRecogGL(18,5);;
Stamp: ClassicalNatural
gap> TestRecogGL(19,5);;
Stamp: ClassicalNatural

#
gap> #TestRecogGL(2,8);; # FIXME: see issue #12
gap> TestRecogGL(3,8);;
Stamp: ClassicalNatural
gap> TestRecogGL(4,8);;
Stamp: ClassicalNatural
gap> TestRecogGL(5,8);;
Stamp: ClassicalNatural
gap> TestRecogGL(6,8);;
Stamp: ClassicalNatural
gap> TestRecogGL(7,8);;
Stamp: ClassicalNatural
gap> TestRecogGL(8,8);;
Stamp: ClassicalNatural
gap> TestRecogGL(9,8);;
Stamp: ClassicalNatural
gap> TestRecogGL(10,8);;
Stamp: ClassicalNatural
gap> TestRecogGL(17,8);;
Stamp: ClassicalNatural
gap> TestRecogGL(18,8);;
Stamp: ClassicalNatural
gap> TestRecogGL(19,8);;
Stamp: ClassicalNatural

#
gap> TestRecogGL(2,9);;
Stamp: ClassicalNatural
gap> TestRecogGL(3,9);;
Stamp: ClassicalNatural
gap> TestRecogGL(4,9);;
Stamp: ClassicalNatural
gap> TestRecogGL(5,9);;
Stamp: ClassicalNatural
gap> TestRecogGL(6,9);;
Stamp: ClassicalNatural
gap> TestRecogGL(7,9);;
Stamp: ClassicalNatural
gap> TestRecogGL(8,9);;
Stamp: ClassicalNatural
gap> TestRecogGL(9,9);;
Stamp: ClassicalNatural
gap> TestRecogGL(10,9);;
Stamp: ClassicalNatural
gap> TestRecogGL(17,9);;
Stamp: ClassicalNatural
gap> TestRecogGL(18,9);;
Stamp: ClassicalNatural
gap> #TestRecogGL(19,9);; # disabled to speedup this .tst file

#
gap> #TestRecogGL(2,16);; # FIXME: see issue #12
gap> TestRecogGL(3,16);;
Stamp: ClassicalNatural
gap> TestRecogGL(4,16);;
Stamp: ClassicalNatural
gap> TestRecogGL(5,16);;
Stamp: ClassicalNatural
gap> TestRecogGL(6,16);;
Stamp: ClassicalNatural
gap> TestRecogGL(7,16);;
Stamp: ClassicalNatural
gap> TestRecogGL(8,16);;
Stamp: ClassicalNatural
gap> TestRecogGL(9,16);;
Stamp: ClassicalNatural
gap> TestRecogGL(10,16);;
Stamp: ClassicalNatural
gap> TestRecogGL(17,16);;
Stamp: ClassicalNatural
gap> #TestRecogGL(18,16);; # disabled to speedup this .tst file
gap> #TestRecogGL(19,16);; # disabled to speedup this .tst file

#
gap> TestRecogGL(2,25);;
Stamp: ClassicalNatural
gap> TestRecogGL(3,25);;
Stamp: ClassicalNatural
gap> TestRecogGL(4,25);;
Stamp: ClassicalNatural
gap> TestRecogGL(5,25);;
Stamp: ClassicalNatural
gap> TestRecogGL(6,25);;
Stamp: ClassicalNatural
gap> TestRecogGL(7,25);;
Stamp: ClassicalNatural
gap> TestRecogGL(8,25);;
Stamp: ClassicalNatural
gap> TestRecogGL(9,25);;
Stamp: ClassicalNatural
gap> TestRecogGL(10,25);;
Stamp: ClassicalNatural
gap> #TestRecogGL(17,25);; # disabled to speedup this .tst file
gap> #TestRecogGL(18,25);; # disabled to speedup this .tst file
gap> #TestRecogGL(19,25);; # disabled to speedup this .tst file

#
gap> TestRecogGL(2,27);;
Stamp: ClassicalNatural
gap> TestRecogGL(3,27);;
Stamp: ClassicalNatural
gap> TestRecogGL(4,27);;
Stamp: ClassicalNatural
gap> TestRecogGL(5,27);;
Stamp: ClassicalNatural
gap> TestRecogGL(6,27);;
Stamp: ClassicalNatural
gap> TestRecogGL(7,27);;
Stamp: ClassicalNatural
gap> TestRecogGL(8,27);;
Stamp: ClassicalNatural
gap> TestRecogGL(9,27);;
Stamp: ClassicalNatural
gap> TestRecogGL(10,27);;
Stamp: ClassicalNatural
gap> #TestRecogGL(17,27);; # disabled to speedup this .tst file
gap> #TestRecogGL(18,27);; # disabled to speedup this .tst file
gap> #TestRecogGL(19,27);; # disabled to speedup this .tst file
