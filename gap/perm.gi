#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This files's authors include Max Neunhöffer, Ákos Seress.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
##
##  A collection of find homomorphism methods for permutation groups.
##
#############################################################################

#! @BeginChunk MovesOnlySmallPoints
#! If a permutation group moves only small points
#! (currently, this means that its largest moved point is at most 10),
#! then this method computes a stabilizer chain for the group via
#! <Ref Subsect="StabChain" Style="Text"/>.
#! This is because the most convenient way of solving constructive membership
#! in such a group is via a stabilizer chain.
#! In this case, the calling node becomes a leaf node of the composition tree.
#!
#! If the input group moves a large point (currently, this means a point
#! larger than 10), then this method returns <K>NeverApplicable</K>.
#! @EndChunk
FindHomMethodsPerm.MovesOnlySmallPoints := function(ri, G)
  if LargestMovedPoint(G) <= 10 then
      return FindHomMethodsPerm.StabChain(ri, G);
  fi;
  return NeverApplicable;
end;

#! @BeginChunk NonTransitive
#! If a permutation group <A>G</A> acts nontransitively then this method
#! computes a homomorphism to the action of <A>G</A> on the orbit of the
#! largest moved point. If <A>G</A> is transitive then the method returns
#! <K>NeverApplicable</K>.
#! @EndChunk
FindHomMethodsPerm.NonTransitive :=
  function( ri, G )
    local hom,la,o;

    # Then test whether we can do something:
    if IsTransitive(G) then
        return NeverApplicable;
    fi;

    la := LargestMovedPoint(G);
    o := Orb(G,la,OnPoints);
    Enumerate(o);
    hom := OrbActionHomomorphism(G,o);
    Setvalidatehomominput(ri, {ri,p} -> ForAll(o, x -> (x^p in o)));
    SetHomom(ri,hom);
    return Success;
  end;

#! @BeginChunk Imprimitive
#! If the input group is not known to be transitive then this method
#! returns <K>NotEnoughInformation</K>. If the input group is known to be transitive
#! and primitive then the method returns <K>NeverApplicable</K>; otherwise, the method
#! tries to compute a nontrivial block system. If successful then a
#! homomorphism to the action on the blocks is defined; otherwise,
#! the method returns <K>NeverApplicable</K>.
#! 
#! If the method is successful then it also gives a hint for the children of
#! the node by determining whether the kernel of the action on the
#! block system is solvable. If the answer is yes then the default value 20
#! for the number of random generators in the kernel construction is increased
#! by the number of blocks.
#! @EndChunk
FindHomMethodsPerm.Imprimitive :=
  function( ri, G )
    local blocks,hom,pcgs,subgens;

    # Only look for primitivity once we know transitivity:
    # This ensures the right trying order even if the ranking is wrong.
    if not HasIsTransitive(G) then
        return NotEnoughInformation;
    fi;

    # We test for known non-primitivity:
    if HasIsPrimitive(G) and IsPrimitive(G) then
        return NeverApplicable;   # never call us again
    fi;

    RECOG.SetPseudoRandomStamp(G,"Imprimitive");

    # Now try to work:
    blocks := MaximalBlocks(G,MovedPoints(G));
    if Length(blocks) = 1 then
        SetIsPrimitive(G,true);
        return NeverApplicable;   # never call us again
    fi;

    # Find the homomorphism:
    hom := ActionHomomorphism(G,blocks,OnSets);
    Setvalidatehomominput(ri, {ri,p} -> OnSetsSets(blocks, p) = blocks);
    SetHomom(ri,hom);

    # Now we want to help recognising the kernel, we first check, whether
    # the restriction to one block is solvable, which would mean, that
    # the kernel is solvable and that a hint is in order:
    Setimmediateverification(ri,true);
    forkernel(ri).blocks := blocks;
    Add(forkernel(ri).hints,rec(method := FindHomMethodsPerm.PcgsForBlocks,
                                rank := 400,
                                stamp := "PcgsHinted"));
    Add(forkernel(ri).hints,rec(method := FindHomMethodsPerm.BalTreeForBlocks,
                                rank := 200,
                                stamp := "BalTreeForBlocks"));
    findgensNmeth(ri).args[1] := Length(blocks)+3;
    findgensNmeth(ri).args[2] := 5;
    return Success;
  end;

#! @BeginChunk PcgsForBlocks
#! This method is called after a hint is set in
#! <Ref Subsect="Imprimitive" Style="Text"/>.
#! Therefore, the group <A>G</A> preserves a non-trivial block system.
#! This method checks whether or not the restriction of <A>G</A> on one block
#! is solvable.
#! If so, then <Ref Subsect="Pcgs" Style="Text"/> is called,
#! and otherwise <K>NeverApplicable</K> is returned.
#! @EndChunk
FindHomMethodsPerm.PcgsForBlocks := function(ri,G)
  local blocks,pcgs,subgens;
  blocks := ri!.blocks;   # we know them from above!
  subgens := List(GeneratorsOfGroup(G),g->RestrictedPerm(g,blocks[1]));
  pcgs := Pcgs(Group(subgens));
  if pcgs <> fail then
      # We now know that the kernel is solvable, go directly to
      # the Pcgs method:
      return FindHomMethodsPerm.Pcgs(ri,G);
  fi;
  # We have failed, let others do the work...
  return NeverApplicable;
end;

#! @BeginChunk BalTreeForBlocks
#! This method creates a balanced composition tree for the kernel of an
#! imprimitive group. This is guaranteed as the method is just called
#! from <Ref Subsect="Imprimitive" Style="Text"/> and itself.
#! The homomorphism for the split in the composition tree used is
#! induced by the action of <A>G</A> on
#! half of its blocks.
#! @EndChunk
FindHomMethodsPerm.BalTreeForBlocks := function(ri,G)
  local blocks,cut,hom,lowerhalf,nrblocks,o,upperhalf,l,n,seto;

  blocks := ri!.blocks;

  # We do exactly the same as in the non-transitive case, however,
  # we restrict to about half the blocks and pass our knowledge on:
  nrblocks := Length(blocks);
  if nrblocks = 1 then
      # this might happen during the descent into the tree
      return NeverApplicable;
  fi;
  cut := QuoInt(nrblocks,2);  # this is now at least 1
  lowerhalf := blocks{[1..cut]};
  upperhalf := blocks{[cut+1..nrblocks]};
  o := Concatenation(upperhalf);
  # The order of 'o' in the homom must align with forfactor(ri).blocks below
  hom := ActionHomomorphism(G,o);

  # Make a set so checking validatehomominput is faster
  seto := Immutable(Set(o));
  Setvalidatehomominput(ri, {ri,p} -> ForAll(o, x -> x^p in seto));
  SetHomom(ri,hom);
  Setimmediateverification(ri,true);
  findgensNmeth(ri).args[1] := 3+cut;
  findgensNmeth(ri).args[2] := 5;
  if nrblocks - cut > 1 then
      l := Length(upperhalf[1]);
      n := Length(upperhalf);
      forfactor(ri).blocks := List([1..n],i->[(i-1)*l+1..i*l]);
      Add(forfactor(ri).hints,rec(method := FindHomMethodsPerm.BalTreeForBlocks,
                                  rank := 200,
                                  stamp := "BalTreeForBlocks"),1);
  fi;
  if cut > 1 then
      forkernel(ri).blocks := lowerhalf;
      Add(forkernel(ri).hints,rec(method := FindHomMethodsPerm.BalTreeForBlocks,
                                  rank := 200,
                                  stamp := "BalTreeForBlocks"),1);
  fi;
  return Success;
end;

# Now to the small base groups using stabilizer chains:

# The GAP manual suggests that the labels at each level of a stabiliser chain
# are identical GAP objects, but it does not promise this.
# This function tests whether the stabiliser chain has this property, and
# gives an error if not.
DoSafetyCheckStabChain := function(S)
  while IsBound(S.stabilizer) do
      if not IsIdenticalObj(S.labels, S.stabilizer.labels) then
          ErrorNoReturn("Alert! labels not identical on different levels!");
      fi;
      S := S.stabilizer;
  od;
end;

#! @BeginChunk StabChain
#! This is the randomized &GAP; library function for computing a stabiliser
#! chain. The method selection process ensures that this function is called
#! only with small-base inputs, where the method works efficiently.
#! @EndChunk
FindHomMethodsPerm.StabChain :=
   function( ri, G )
     local Gmem,S,si;

     # We know transitivity and primitivity, because there are higher ranked
     # methods checking for them!

     # Calculate a stabilizer chain:
     Gmem := GroupWithMemory(G);
     if HasStabChainMutable(G) or HasStabChainImmutable(G) or HasSize(G) then
         si := Size(G);
         S := StabChainOp(Gmem,rec(random := 900,size := si));
     else
         S := StabChainOp(Gmem,rec(random := 900));
     fi;
     DoSafetyCheckStabChain(S);
     Setslptonice(ri,SLPOfElms(S.labels));
     StripStabChain(S);
     SetNiceGens(ri,S.labels);
     MakeImmutable(S);
     ri!.stabilizerchain := S;
     Setslpforelement(ri,SLPforElementFuncsPerm.StabChain);
     SetFilterObj(ri,IsLeaf);
     SetSize(G,SizeStabChain(S));
     SetSize(ri,SizeStabChain(S));
     ri!.Gnomem := G;
     return Success;
   end;

SLPforElementFuncsPerm.StabilizerChainPerm := function(ri,x)
  local r;
  r := SiftGroupElementSLP(ri!.stabilizerchain,x);
  return r.slp;
end;

#! @BeginChunk StabilizerChainPerm
#! TODO
#! @EndChunk
# TODO: merge FindHomMethodsPerm.StabilizerChainPerm and  FindHomMethodsProjective.StabilizerChainProj ?
FindHomMethodsPerm.StabilizerChainPerm := function(ri,G)
  local Gm,S;
  Gm := Group(ri!.gensHmem);
  Gm!.pseudorandomfunc := [rec(
     func := function(ri) return RandomElm(ri,"StabilizerChainPerm",true).el; end,
     args := [ri])];
  S := StabilizerChain(Gm);
  SetSize(ri,Size(S));
  SetSize(Grp(ri),Size(S));
  ri!.stabilizerchain := S;
  Setslptonice(ri,SLPOfElms(StrongGenerators(S)));
  ForgetMemory(S);
  Setslpforelement(ri,SLPforElementFuncsPerm.StabilizerChainPerm);
  SetFilterObj(ri,IsLeaf);
  return Success;
end;

# creates recursively a word for <g> using the Schreier tree labels
# from the stabilizer chain <S>
WordinLabels := function(word,S,g)
  local i,point,start;
  if not (IsBound(S.orbit) and IsBound(S.orbit[1])) then
      return fail;
  fi;
  start := S.orbit[1];
  point := start^g;
  while point <> start do
      if not IsBound(S.translabels[point]) then
          return fail;
      fi;
      i := S.translabels[point];
      g := g * S.labels[i];
      point := point^S.labels[i];
      Add(word,i);
  od;
  # now g is in the first stabilizer
  if g <> S.identity then
      if not IsBound(S.stabilizer) then
          return fail;
      fi;
      return WordinLabels(word,S.stabilizer,g);
  fi;
  return word;
end;

# creates a straight line program for an element <g> using the
# Schreier tree labels from the stabilizer chain <S>
SLPinLabels := function(S,g)
  local i,j,l,line,word;
  word := WordinLabels([],S,g);
  if word = fail then
      return fail;
  fi;
  line := [];
  i := 1;
  while i <= Length(word) do
      # Find repeated labels:
      j := i+1;
      while j < Length(word) and word[j] = word[i] do
          j := j + 1;
      od;
      Add(line,word[i]);
      Add(line,j-i);
      i := j;
  od;
  l := Length(S!.labels);
  if Length(word) = 0 then
      return StraightLineProgramNC([[1, 0]], l);
  fi;
  return StraightLineProgramNC([line, [l + 1, -1]], l);
end;


SLPforElementFuncsPerm.StabChain :=
  function( ri, g )
    # we know that g is an element of Grp(ri) all without memory.
    # we know that ri!.stabilizerchain is an immutable StabChain and
    # ri!.stronggensslp is bound to a slp that expresses the strong generators
    # in that StabChain in terms of the GeneratorsOfGroup(Grp(ri)).
    local S,s;
    S := ri!.stabilizerchain;
    return SLPinLabels(S,g);
  end;

StoredPointsPerm := function(p)
  # Determines, as a permutation of how many points p is stored.
  local s;
  s := SIZE_OBJ(p) - GAPInfo.BytesPerVariable;
  if IsPerm4Rep(p) then
      return s/4;   # permutation stored with 4 bytes per point
  elif IsPerm2Rep(p) then
      return s/2;   # permutation stored with 2 bytes per point
  fi;
  ErrorNoReturn("StoredPointsPerm: input is not an internal permutation");
end;

#! @BeginChunk ThrowAwayFixedPoints
#! This method defines a homomorphism of a permutation group
#! <A>G</A> to the action on the moved points of <A>G</A> if
#! <A>G</A> does not have too many moved points. In the current setup, the
#! homomorphism is defined if the number <M>k</M> of moved
#! points is at most <M>1/3</M> of the largest moved point of <A>G</A>,
#! or  <M>k</M> is at most half of the number of points on which
#! <A>G</A> is stored internally by &GAP;. The method returns
#! <K>NeverApplicable</K> if it does not define a homomorphism indicating that it will
#! never succeed.
#! @EndChunk
FindHomMethodsPerm.ThrowAwayFixedPoints :=
  function( ri, G )
      # Check, whether we can throw away fixed points
      local gens,hom,l,n,o;

      gens := GeneratorsOfGroup(G);
      l := List(gens,StoredPointsPerm);
      n := NrMovedPoints(G);
      if 2*n > Maximum(l) or 3*n > LargestMovedPoint(G) then  # we do nothing
          return NeverApplicable;
      fi;
      o := MovedPoints(G);
      hom := ActionHomomorphism(G,o);
      SetHomom(ri,hom);
      Setvalidatehomominput(ri, {ri,p} -> IsSubset(o, MovedPoints(p)));

      # Initialize the rest of the record:
      findgensNmeth(ri).method := FindKernelDoNothing;

      return Success;
  end;

#! @BeginChunk Pcgs
#! This is the &GAP; library function to compute a stabiliser chain for a
#! solvable permutation group. If the method is successful then the calling
#! node becomes a leaf node in the recursive scheme. If the input group is
#! not solvable then the method returns <K>NeverApplicable</K>.
#! @EndChunk
FindHomMethodsPerm.Pcgs :=
  function( ri, G )
    local GM,S,pcgs;
    GM := Group(ri!.gensHmem);
    GM!.pseudorandomfunc := [rec(
       func := function(ri) return RandomElm(ri,"PCGS",true).el; end,
       args := [ri])];
    pcgs := Pcgs(GM);
    if pcgs = fail then
        return NeverApplicable;
    fi;
    S := StabChainMutable(GM);
    DoSafetyCheckStabChain(S);
    Setslptonice(ri,SLPOfElms(S.labels));
    StripStabChain(S);
    SetNiceGens(ri,S.labels);
    MakeImmutable(S);
    ri!.stabilizerchain := S;
    Setslpforelement(ri,SLPforElementFuncsPerm.StabChain);
    SetFilterObj(ri,IsLeaf);
    SetSize(G,SizeStabChain(S));
    SetSize(ri,SizeStabChain(S));
    ri!.Gnomem := G;
    return Success;
  end;


# The following commands install the above methods into the database:

AddMethod(FindHomDbPerm, FindHomMethodsGeneric.TrivialGroup,
          300, "TrivialGroup",
          "just go through generators and compare to the identity");
AddMethod(FindHomDbPerm, FindHomMethodsPerm.ThrowAwayFixedPoints,
          100, "ThrowAwayFixedPoints",
          "try to find a huge amount of (possible internal) fixed points");
AddMethod(FindHomDbPerm, FindHomMethodsGeneric.FewGensAbelian,
          99, "FewGensAbelian",
         "if very few generators, check IsAbelian and if yes, do KnownNilpotent");
AddMethod(FindHomDbPerm, FindHomMethodsPerm.Pcgs,
          97, "Pcgs",
          "use a Pcgs to calculate a stabilizer chain" );
AddMethod(FindHomDbPerm, FindHomMethodsPerm.MovesOnlySmallPoints,
          95, "MovesOnlySmallPoints",
          "calculate a stabilizer chain if only small points are moved");
AddMethod(FindHomDbPerm, FindHomMethodsPerm.NonTransitive,
          90, "NonTransitive",
          "try to find non-transitivity and restrict to orbit");
AddMethod( FindHomDbPerm, FindHomMethodsPerm.Giant,
          80, "Giant",
          "tries to find Sn and An in their natural actions" );
AddMethod(FindHomDbPerm, FindHomMethodsPerm.Imprimitive,
          70, "Imprimitive",
          "for a imprimitive permutation group, restricts to block system");
AddMethod(FindHomDbPerm, FindHomMethodsPerm.LargeBasePrimitive,
          60, "LargeBasePrimitive",
          "recognises large-base primitive permutation groups" );
AddMethod(FindHomDbPerm, FindHomMethodsPerm.StabilizerChainPerm,
          55, "StabilizerChainPerm",
          Concatenation(
              "for a permutation group using a stabilizer chain via the ",
              "<URL Text=\"genss package\">",
              "https://gap-packages.github.io/genss/",
              "</URL>"
          ));
AddMethod(FindHomDbPerm, FindHomMethodsPerm.StabChain,
          50, "StabChain",
          "for a permutation group using a stabilizer chain");

# Note that the last one will always succeed!
