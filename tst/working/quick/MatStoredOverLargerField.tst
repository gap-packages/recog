gap> START_TEST("MatStoredOverLargerField.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);

# Groups whose matrices are stored over a larger field than their entries
# generate, as ClassicalMaximals returns them for subfield subgroups.
gap> StoredOver := {G, f} -> GroupWithGenerators(
>      List(GeneratorsOfGroup(G), g -> ImmutableMatrix(f, g)));;
gap> RecogniseWithSeed := function(G, seed)
>   Reset(GlobalMersenneTwister, seed);
>   Reset(GlobalRandomSource, seed);
>   return RecogniseGroup(G);
> end;;

# a group of order 36 with entries in GF(2), stored over GF(4)
gap> a := [[0,1,1,0],[1,0,0,1],[0,0,0,1],[0,1,0,0]] * Z(2)^0;;
gap> b := [[0,0,0,1],[0,1,1,0],[0,0,1,0],[1,0,0,0]] * Z(2)^0;;
gap> G := StoredOver(Group(a, b), GF(4));;
gap> [FieldOfMatrixGroup(G), DefaultFieldOfMatrixGroup(G)];
[ GF(2), GF(2^2) ]
gap> ri := RecogniseWithSeed(G, 1);;
gap> IsReady(ri) and Size(ri) = 36;
true
gap> ri := RECOG.TestGroup(G, false, 36);;
gap> ri := RECOG.TestGroup(G, true, 36);;

# The root keeps the group it was given, and its nice generators are stored
# like the generators of that group. GAP calls a matrix compressed over GF(2)
# different from the same matrix compressed over GF(4), so SLPs have to
# evaluate to the representation of the element they were asked for.
gap> ri := RecogniseWithSeed(G, 1);;
gap> IsIdenticalObj(Grp(ri), G);
true
gap> fhmethsel(ri).successMethod;
"StoredOverLargerField"
gap> DefaultFieldOfMatrixGroup(Grp(ImageRecogNode(ri)));
GF(2)
gap> x := PseudoRandom(G);;
gap> ResultOfStraightLineProgram(SLPforElement(ri, x), NiceGens(ri)) = x;
true

# an element with an entry outside the field of the group
gap> SLPforElement(ri, Z(4) * x);
fail
gap> ri := RecogniseProjectiveGroup(G);;
gap> slp := SLPforElement(ri, Z(4) * x);;
gap> IsEqualProjective(ResultOfStraightLineProgram(slp, NiceGens(ri)), x);
true
gap> y := List(x, ShallowCopy);; y[1,1] := y[1,1] + Z(4);;
gap> SLPforElement(ri, y);
fail

# Sp(4,2) stored over GF(8)
gap> G := StoredOver(Sp(4,2), GF(8));;
gap> ri := RecogniseWithSeed(G, 2);;
gap> IsReady(ri) and Size(ri) = 720;
true
gap> ri := RECOG.TestGroup(G, false, 720);;

# classical groups in their natural representation over a subfield
gap> G := StoredOver(SL(10,2), GF(4));;
gap> ri := RECOG.TestGroup(G, false, Size(SL(10,2)));;
gap> G := StoredOver(Sp(6,4), GF(16));;
gap> ri := RECOG.TestGroup(G, false, Size(Sp(6,4)));;
gap> G := StoredOver(SO(9,3), GF(9));;
gap> ri := RECOG.TestGroup(G, false, Size(SO(9,3)));;

# A node inside the tree can be stored over a larger field as well. In this
# dihedral group of order 30 the subgroup of order 3 has its entries in GF(4)
# and reaches a node with a hint; when the hint does not apply, no other
# method may see that node. List the methods, other than hints and
# TrivialGroup, that succeeded on generators not compressed over the field of
# their node.
gap> MixedStorageMethods := function(ri)
>   local res, stamp, G;
>   res := [];
>   G := Grp(ri);
>   stamp := fhmethsel(ri).successMethod;
>   if IsMatrixGroup(G) and Size(ri!.field) <= 256
>      and not ForAll(GeneratorsOfGroup(G),
>                     g -> RECOG.IsCompressedOverField(g, ri!.field))
>      and not stamp in ["StoredOverLargerField", "TrivialGroup"]
>      and not (IsBound(ri!.hints)
>               and ForAny(ri!.hints, h -> Stamp(h.method) = stamp)) then
>     Add(res, stamp);
>   fi;
>   if not IsLeaf(ri) then
>     Append(res, MixedStorageMethods(ImageRecogNode(ri)));
>     if KernelRecogNode(ri) <> fail then
>       Append(res, MixedStorageMethods(KernelRecogNode(ri)));
>     fi;
>   fi;
>   return res;
> end;;
gap> z := Z(16);;
gap> G := Group([[0*z, z^0], [z^0, 0*z]], [[z, 0*z], [0*z, z^-1]]);;
gap> ri := RecogniseWithSeed(G, 1);;
gap> IsReady(ri) and Size(ri) = 30;
true
gap> MixedStorageMethods(ri);
[  ]
gap> ri := RecogniseWithSeed(StoredOver(Sp(4,2), GF(8)), 2);;
gap> MixedStorageMethods(ri);
[  ]

# nothing to do if the storage fits, or if there is no compressed
# representation
gap> TryMethod := G -> CallRecogMethod(
>      FindHomMethodsMatrix.StoredOverLargerField, RecogNode(G, false));;
gap> TryMethod(SL(3,4)) = NeverApplicable;
true
gap> G := Group(Z(257^2) * IdentityMat(2, GF(257)), IdentityMat(2, GF(257)));;
gap> TryMethod(G) = NeverApplicable;
true
gap> TryMethod(StoredOver(SL(3,2), GF(4))) = Success;
true

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("MatStoredOverLargerField.tst");
