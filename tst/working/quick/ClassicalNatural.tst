gap> START_TEST("ClassicalNatural.tst");

#
gap> ReadPackage("recog", "tst/utils.g");
true

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
gap> #TestRecogGL(7,3);; # FIXME: Stamp: StabilizerChainProj
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
gap> #TestRecogGL(6,5);; # FIXME: Stamp: StabilizerChainProj

#
gap> #TestRecogGL(2,8);; # FIXME: see issue #12
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
gap> #TestRecogGL(2,16);; # FIXME: see issue #12
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
