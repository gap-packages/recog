# TODO is this exclusively for code in gap/matrix/classical.gi?
# Tests for non-generic classical groups
# for the non-generic parameters see the paper [NP99].

# Tests for generic classical groups
# TODO what to put into ClassicalNatural.tst?
TestRecogGL := function(d,q)
    local h, gens, g, ri, r, stamp;
    h := GL(d,q);
    gens := List([1..10],x->PseudoRandom(h));
    # FIXME: while this is a generating set with HIGH PROBABILITY, it is not
    # always one.  This could lead to spurious failures in the test suite...
    g := GroupWithGenerators(gens);
    ri := RECOG.TestGroup(g,false,Size(h));
    r := ri;
    if not IsLeaf(ri) then r := RIFac(ri); fi;
    stamp := r!.fhmethsel.successMethod;
    if stamp="ProjDeterminant" then
        r := RIKer(r);
        stamp := r!.fhmethsel.successMethod;
    fi;
    Print("Stamp: ",stamp,"\n");
    return ri;
end;;

SU
Sp


SO(d, q)
Omega(d, q)
# even characteristic
Omega(e, d, q)
SO(e, d, q)

# Special semilinear
SigmaL








# A run with SU(3, 5)
gap> g := SU(3,5);;
gap> SetInfoLevel(InfoClassical, 2);
gap> res := RecogniseClassical(g);;
#I  G is not an alternating group
#I  G' is not a Mathieu group;
#I  involution in cyclic subgroup  of order 8 is not central
#I  group contains SU(3, 25);
gap> DisplayRecog(res);
Reducible : false
Forms: unitary
E : [ 3 ]
LE : [ 3 ]
BE : [ 3 ]
LB : [ 3 ]
Mathieu ruled out: true
An ruled out: true
PSL ruled out: true
orders [ 5, 6, 8, 10, 12, 21, 30 ]
porders [ [ 4, Z(5^2)^8 ], [ 4, Z(5^2)^16 ], [ 5, Z(5)^0 ], [ 6, Z(5)^0 ], [ 7, Z(5^2)^8 ], [ 7, Z(5^2)^16 ], [ 8, Z(5)^0 ], [ 10, Z(5)^0 ], [ 10, Z(5^2)^16 ] ]
--------> contains Sp(3,25)
--------> contains SU(3,5)

gap> # recog recognises U3 and passes a hint to the stabchain method
gap> RecogniseGroup(g);
#I  G is not an alternating group
#I  G' is not a Mathieu group;
#I  involution in cyclic subgroup  of order 8 is not central
#I  group contains SU(3, 25);
K dim=   3 field=25  0
<recoginfo GoProjective Dim=3 Field=25
 F:<recoginfo (projective) StabilizerChainProj_U3(5) Size=126000 Dim=3 Field=25>
 K:<recoginfo DiagonalMatrices Dim=3 Field=25
    F:<recoginfo Scalar Dim=1 Field=25>
    K:<trivial kernel>>
