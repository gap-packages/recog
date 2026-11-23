#
# Factor records: orders and normal form against the GAP library.
# IsomorphismTypeInfoFiniteSimpleGroup returns no series for an order that
# two simple groups share.
#
gap> names := [];;
gap> for series in ["L","U","S","O","O+","O-"] do
>   for d in [2..9] do
>     for q in [2,3,4,5,7,8,9] do
>       Add(names, [series, [d,q]]);
>     od;
>   od;
> od;
gap> for q in [2,3,4,5,7,8,9] do
>   Append(names, [ ["G",[2,q]], ["3D",[4,q]] ]);
> od;
gap> for q in [2,3,4] do
>   Append(names, [ ["F",[4,q]], ["2E",[6,q]], ["E",[6,q]], ["E",[7,q]],
>                   ["E",[8,q]] ]);
> od;
gap> for q in [2,8,32] do
>   Append(names, [ ["Sz",[q]], ["2F",[q]] ]);
> od;
gap> Append(names, List([3,27,243], q -> ["2G",[q]]));
gap> Append(names, List([5..12], n -> ["A",[n]]));
gap> Append(names, List(RECOG.SporadicsNames{[1..RECOG_NrSporadicGroups]},
>                       name -> ["Spor",[name]]));
gap> nr := 0;; bad := [];; shared := [];;
gap> for x in names do
>   nf := RECOG.SimpleGroupNormalForm(x[1], x[2]);
>   if RECOG.IsSimpleGroupName(nf[1], nf[2]) then
>     nr := nr + 1;
>     f := RECOG.SimpleFactor(x[1], x[2]);
>     info := IsomorphismTypeInfoFiniteSimpleGroup(f.order);
>     if info = fail then
>       Add(bad, x);
>     elif not IsBound(info.series) then
>       AddSet(shared, f.name);
>     elif RECOG.SimpleFactorFromTypeInfo(info) <> f then
>       Add(bad, x);
>     fi;
>   fi;
> od;
gap> nr; bad;
261
[  ]
gap> shared;
[ "A8", "L3(4)", "O7(3)", "O7(5)", "O7(7)", "O7(9)", "O9(3)", "O9(5)", 
  "O9(7)", "O9(9)", "S6(3)", "S6(5)", "S6(7)", "S6(9)", "S8(3)", "S8(5)", 
  "S8(7)", "S8(9)" ]
gap> List([ ["L",[2,4]], ["L",[2,5]], ["L",[2,9]], ["L",[3,2]], ["L",[4,2]],
>         ["U",[4,2]], ["O",[3,7]], ["O",[5,3]], ["O",[7,2]], ["O+",[6,3]],
>         ["O-",[4,3]], ["O-",[6,3]], ["O+",[8,2]], ["2F",[2]] ],
>      x -> RECOG.SimpleFactor(x[1], x[2]).name);
[ "A5", "A5", "A6", "L2(7)", "A8", "S4(3)", "L2(7)", "S4(3)", "S6(2)", 
  "L4(3)", "A6", "U4(3)", "O8+(2)", "2F4(2)'" ]
gap> RECOG.SimpleFactor("U", [4,3]);
rec( name := "U4(3)", order := 3265920, parameter := [ 4, 3 ], series := "U" )
gap> RECOG.SimpleFactor("L", [2,3]);
Error, <series> = L and <parameter> = [ 2, 3 ] do not describe a simple group
gap> RECOG.SimpleFactor("O+", [4,3]);
Error, <series> = O+ and <parameter> = [ 4, 3 ] do not describe a simple group

#
# the names in the hint database
#
gap> ForAll(RecNames(RECOG.AlmostSimpleHints), name ->
>      ForAll(RECOG.AlmostSimpleHints.(name), hint -> not IsBound(hint.size)
>        or Product(RECOG.LeafDataForHint(name).factors, f -> f.order)
>           = hint.size));
true
gap> List(["M11", "J2.2", "2F4(2)'.2", "L2(31)"],
>         name -> RECOG.LeafDataForHint(name).type);
[ "simple", "almostsimple", "almostsimple", "unknown" ]
gap> RECOG.LeafDataForHint("J2.2");
rec( 
  factors := 
    [ 
      rec( name := "J2", order := 604800, parameter := [ "J2" ], 
          series := "Spor" ), 
      rec( name := "C2", order := 2, parameter := [ 2 ], series := "Z" ) ], 
  nicegens := "strong", proven := false, type := "almostsimple" )

#
# permutation groups
#
gap> oldOrbInfoLevel := InfoLevel(InfoOrb);;
gap> SetInfoLevel(InfoOrb, 0); # genss may warn "Schreier tree is not shallow"
gap> factors := function(g)
>   local ri, f;
>   ri := RECOG.TestGroup(g, false, Size(g));
>   f := CompositionFactorsOfRecogNode(ri);
>   if Product(f, x -> x.order) <> Size(ri) then
>     Error("orders of the factors do not multiply to the size");
>   fi;
>   return List(f, x -> x.name);
> end;;
gap> factors(WreathProduct(SymmetricGroup(8), SymmetricGroup(3)));
[ "A8", "C2", "A8", "C2", "A8", "C2", "C3", "C2" ]
gap> factors(WreathProduct(AlternatingGroup(5), Group((1,2,3))));
[ "A5", "A5", "A5", "C3" ]
gap> factors(WreathProduct(SymmetricGroup(4), SymmetricGroup(3)));
[ "C2", "C2", "C2", "C2", "C2", "C2", "C3", "C3", "C3", "C2", "C2", "C2", 
  "C3", "C2" ]
gap> factors(Action(SymmetricGroup(9), Combinations([1..9], 2), OnSets));
[ "A9", "C2" ]
gap> factors(Group(()));
[  ]

#
# matrix groups
#
gap> factors(GL(4,3));
[ "C2", "L4(3)", "C2" ]
gap> factors(GL(6,5));
[ "C2", "C2", "L6(5)", "C2" ]
gap> factors(GL(2,3));
[ "C2", "C2", "C2", "C3", "C2" ]
gap> factors(GL(2,4));
[ "C3", "A5" ]
gap> factors(GL(2,9));
[ "C2", "C2", "C2", "A6", "C2" ]
gap> factors(GL(3,2));
[ "L2(7)" ]

# the stabiliser in GL(4,4) of a subspace of dimension 2, of shape
# 2^8:(GL(2,4) x GL(2,4))
gap> id := IdentityMat(4, GF(4));;
gap> embed := function(m, pos)
>   local x;
>   x := MutableCopyMat(id);
>   x{pos}{pos} := m;
>   return x;
> end;;
gap> gens := Concatenation(
>      List(GeneratorsOfGroup(GL(2,4)), m -> embed(m, [1,2])),
>      List(GeneratorsOfGroup(GL(2,4)), m -> embed(m, [3,4])));;
gap> u := MutableCopyMat(id);; u[3,1] := Z(4)^0;; Add(gens, u);
gap> factors(Group(gens));
[ "C2", "C2", "C2", "C2", "C2", "C2", "C2", "C2", "C3", "C3", "A5", "A5" ]

#
# projective groups
#
gap> ri := RECOG.TestGroup(Sp(4,3), true, Size(Sp(4,3)) / 2);;
gap> List(CompositionFactorsOfRecogNode(ri), f -> f.name);
[ "S4(3)" ]
gap> ri := RECOG.TestGroup(GL(4,3), true, Size(GL(4,3)) / 2);;
gap> List(CompositionFactorsOfRecogNode(ri), f -> f.name);
[ "L4(3)", "C2" ]

#
# the records of the leaves
#
# Giant and ClassicalNatural give up with small probability, and another
# method then makes the leaf. Recognise until the wanted method did.
gap> leafOf := function(g, method)
>   local ri, leaf;
>   repeat
>     ri := RECOG.TestGroup(g, false, Size(g));
>     leaf := First(RECOG.Leaves(ri),
>                   x -> fhmethsel(x).successMethod = method);
>   until leaf <> fail;
>   return leaf;
> end;;
gap> LeafData(leafOf(GL(6,5), "ClassicalNatural"));
rec( 
  factors := 
    [ 
      rec( name := "L6(5)", order := 1383059427750000000000000, 
          parameter := [ 6, 5 ], series := "L" ) ], nicegens := "SL", 
  proven := true, scalars := 2, type := "simple" )
gap> data := LeafData(leafOf(GL(6,5), "Scalar"));;
gap> data.type; data.pcgs; data.relativeOrders;
"soluble"
[ 1 ]
[ 4 ]
gap> data := LeafData(leafOf(SymmetricGroup(11), "Giant"));;
gap> data.type; data.nicegens; data.proven;
"almostsimple"
"SnAn"
true
gap> leaf := leafOf(SymmetricGroup(4), "Pcgs");;
gap> data := LeafData(leaf);;
gap> data.pcgs; data.relativeOrders;
[ 2, 3, 4, 5 ]
[ 2, 3, 2, 2 ]
gap> IsOne(NiceGens(leaf)[1]);
true

# The black-box recognition of SL(d,q) accepts a quotient of SL(d,q) by a
# central subgroup. No group above reaches it, so call it directly. The
# centre of SL(3,4) has order 3 and consists of scalars.
gap> blackBoxSL := function(g, projective, d, q)
>   local ri;
>   ri := RecogNode(g, projective);
>   repeat
>   until SLCR.FindHom(ri, g, d, q) = Success;
>   SetFilterObj(ri, IsReady);
>   return ri;
> end;;
gap> leaf := blackBoxSL(SL(3,4), false, 3, 4);;
gap> data := LeafData(leaf);;
gap> data.type; data.proven; List(data.factors, f -> f.name);
"quasisimple"
false
[ "C3", "L3(4)" ]
gap> RECOG.CheckLeafData(leaf);
true
gap> data := LeafData(blackBoxSL(SL(3,4), true, 3, 4));;
gap> data.type; List(data.factors, f -> f.name);
"simple"
[ "L3(4)" ]

# a leaf of unknown type gets its factors on first use
gap> ri := RECOG.TestGroup(SymmetricGroup(6), false, 720);;
gap> LeafData(ri);
rec( nicegens := "strong", proven := true, type := "unknown" )
gap> List(CompositionFactorsOfRecogNode(ri), f -> f.name);
[ "A6", "C2" ]
gap> IsBound(LeafData(ri).factors);
true
gap> LeafData(ri).type;
"unknown"
gap> ri := RECOG.TestGroup(AlternatingGroup(7), false, 2520);;
gap> LeafData(ri).type;
"unknown"
gap> List(CompositionFactorsOfRecogNode(ri), f -> f.name);
[ "A7" ]
gap> LeafData(ri).type;
"simple"

#
# leaves whose method sets no LeafData
#
gap> ri := RecogNode(SymmetricGroup(5), false, rec());;
gap> SetFilterObj(ri, IsLeaf); SetFilterObj(ri, IsReady);
gap> LeafData(ri);
rec( proven := true, type := "unknown" )
gap> List(CompositionFactorsOfRecogNode(ri), f -> f.name);
[ "A5", "C2" ]
gap> ri := RecogNode(Group(()), false, rec());;
gap> SetFilterObj(ri, IsLeaf); SetFilterObj(ri, IsReady);
gap> LeafData(ri);
rec( factors := [  ], proven := true, type := "soluble" )
gap> ri := RecogNode(GL(2,5), false, rec());;
gap> SetFilterObj(ri, IsLeaf); SetFilterObj(ri, IsReady);
gap> CompositionFactorsOfRecogNode(ri);
Error, the leaf <ri> has neither composition factors in LeafData(<ri>) nor a s\
tabiliser chain

#
# display
#
gap> DisplayCompositionFactors(RECOG.TestGroup(GL(4,3), false, Size(GL(4,3))));
Group of size 24261120
 | C2
Group of size 12130560
 | L4(3)
Group of size 2
 | C2
1
gap> DisplayCompositionFactors(RECOG.TestGroup(Group(()), false, 1));
1
gap> ri := RecogNode(SymmetricGroup(5), false, rec());;
gap> DisplayCompositionFactors(ri);
Recognition failed
gap> CompositionFactorsOfRecogNode(ri);
Error, the recognition described by this recognition node has failed!
gap> SetInfoLevel(InfoOrb, oldOrbInfoLevel);
