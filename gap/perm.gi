#############################################################################
##
##  perm.gi
##                                recog package
##                                                        Max Neunhoeffer
##                                                            Ákos Seress
##
##  Copyright 2005-2008 by the authors.
##  This file is free software, see license information at the end.
##
##  A collection of find homomorphism methods for permutation groups.
##
#############################################################################

# We first want to get rid of the trivial group:

SLPforElementFuncsPerm.TrivialPermGroup :=
   function(ri,g)
     return StraightLineProgram( [ [1,0] ], 1 );
   end;

FindHomMethodsPerm.TrivialPermGroup := function(ri, G)
  local gens;
  gens := GeneratorsOfGroup(G);
  if not ForAll(gens, ri!.isone) then
      return NeverApplicable;
  fi;
  SetSize(ri, 1);
  Setslpforelement(ri, SLPforElementFuncsPerm.TrivialPermGroup);
  Setslptonice(ri, StraightLineProgramNC([[[1,0]]],Length(gens)));
  SetFilterObj(ri, IsLeaf);
  return Success;
end;

FindHomMethodsPerm.VeryFewPoints := function(ri, G)
  if LargestMovedPoint(G) <= 10 then
      return FindHomMethodsPerm.StabChain(ri, G);
  else
      return NeverApplicable;
  fi;
end;

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
    SetHomom(ri,hom);
    return Success;
  end;

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

FindHomMethodsPerm.PcgsForBlocks := function(ri,G)
  local blocks,pcgs,subgens;
  blocks := ri!.blocks;   # we know them from above!
  subgens := List(GeneratorsOfGroup(G),g->RestrictedPerm(g,blocks[1]));
  pcgs := Pcgs(Group(subgens));
  if subgens <> fail then
      # We now know that the kernel is solvable, go directly to
      # the Pcgs method:
      return FindHomMethodsPerm.Pcgs(ri,G);
  fi;
  # We have failed, let others do the work...
  return NeverApplicable;
end;

FindHomMethodsPerm.BalTreeForBlocks := function(ri,G)
  local blocks,cut,hom,lowerhalf,nrblocks,o,upperhalf,l,n;

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
  hom := ActionHomomorphism(G,o);
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

DoSafetyCheckStabChain := function(S)
  while IsBound(S.stabilizer) do
      if not(IsIdenticalObj(S.labels,S.stabilizer.labels)) then
          Error("Alert! labels not identical on different levels!");
      fi;
      S := S.stabilizer;
  od;
end;

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
     SetStabChainImmutable(G,S);
     Setslpforelement(ri,SLPforElementFuncsPerm.StabChain);
     SetFilterObj(ri,IsLeaf);
     SetSize(G,SizeStabChain(S));
     SetSize(ri,SizeStabChain(S));
     ri!.Gnomem := G;
     return Success;
   end;

SLPforElementFuncsPerm.StabilizerChain := function(ri,x)
  local r;
  r := SiftGroupElementSLP(ri!.stabilizerchain,x);
  return r.slp;
end;

FindHomMethodsPerm.StabilizerChain := function(ri,G)
  local Gm,S;
  Gm := Group(ri!.gensHmem);
  Gm!.pseudorandomfunc := [rec(
     func := function(ri) return RandomElm(ri,"StabilizerChain",true).el; end,
     args := [ri])];
  S := StabilizerChain(Gm);
  SetSize(ri,Size(S));
  SetSize(Grp(ri),Size(S));
  ri!.stabilizerchain := S;
  Setslptonice(ri,SLPOfElms(StrongGenerators(S)));
  ForgetMemory(S);
  Setslpforelement(ri,SLPforElementFuncsPerm.StabilizerChain);
  SetFilterObj(ri,IsLeaf);
  return Success;
end;

WordinLabels := function(word,S,g)
  local i,point,start;
  if not(IsBound(S.orbit) and IsBound(S.orbit[1])) then
      return fail;
  fi;
  start := S.orbit[1];
  point := start^g;
  while point <> start do
      if not(IsBound(S.translabels[point])) then
          return fail;
      fi;
      i := S.translabels[point];
      g := g * S.labels[i];
      point := point^S.labels[i];
      Add(word,i);
  od;
  # now g is in the first stabilizer
  if g <> S.identity then
      if not(IsBound(S.stabilizer)) then
          return fail;
      fi;
      return WordinLabels(word,S.stabilizer,g);
  fi;
  return word;
end;

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
      return StraightLineProgramNC( [ [1,0] ], l );
  else
      return StraightLineProgramNC( [ line, [l+1,-1] ], l );
  fi;
end;


SLPforElementFuncsPerm.StabChain :=
  function( ri, g )
    # we know that g is an element of Grp(ri) all without memory.
    # we know that Grp(ri) has an immutable StabChain and
    # ri!.stronggensslp is bound to a slp that expresses the strong generators
    # in that StabChain in terms of the GeneratorsOfGroup(Grp(ri)).
    local G,S,s;
    G := ri!.Gnomem;
    S := StabChainImmutable(G);
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
  else
      Error("StoredPointsPerm: input is not an internal permutation");
  fi;
end;

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

      # Initialize the rest of the record:
      findgensNmeth(ri).method := FindKernelDoNothing;

      return Success;
  end;

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
    SetStabChainImmutable(G,S);
    Setslpforelement(ri,SLPforElementFuncsPerm.StabChain);
    SetFilterObj(ri,IsLeaf);
    SetSize(G,SizeStabChain(S));
    SetSize(ri,SizeStabChain(S));
    ri!.Gnomem := G;
    return Success;
  end;


# The following commands install the above methods into the database:

AddMethod(FindHomDbPerm, FindHomMethodsPerm.TrivialPermGroup,
          300, "TrivialPermGroup",
          "just go through generators and compare to the identity");
AddMethod(FindHomDbPerm, FindHomMethodsPerm.ThrowAwayFixedPoints,
          100, "ThrowAwayFixedPoints",
          "try to find a huge amount of (possible internal) fixed points");
AddMethod(FindHomDbPerm, FindHomMethodsProjective.FewGensAbelian,
          99, "FewGensAbelian",
     "if very few generators, check IsAbelian and if yes, do KnownNilpotent");
AddMethod(FindHomDbPerm, FindHomMethodsPerm.Pcgs,
          97, "Pcgs",
          "use a Pcgs to calculate a StabChain" );
AddMethod(FindHomDbPerm, FindHomMethodsPerm.VeryFewPoints,
          95, "VeryFewPoints",
          "calculate a stabchain if we act on very few points");
AddMethod(FindHomDbPerm, FindHomMethodsPerm.NonTransitive,
          90, "NonTransitive",
          "try to find non-transitivity and restrict to orbit");
AddMethod( FindHomDbPerm, FindHomMethodsPerm.Giant,
          80, "Giant",
          "tries to find Sn and An" );
AddMethod(FindHomDbPerm, FindHomMethodsPerm.Imprimitive,
          70, "Imprimitive",
          "for a imprimitive permutation group, restricts to block system");
AddMethod(FindHomDbPerm, FindHomMethodsPerm.SnkSetswrSr,
          60, "SnkSetswrSr",
          "tries to find jellyfish" );
AddMethod(FindHomDbPerm, FindHomMethodsPerm.StabilizerChain,
          55, "StabilizerChain",
          "for a permutation group using a stabilizer chain (genss)");
AddMethod(FindHomDbPerm, FindHomMethodsPerm.StabChain,
          50, "StabChain",
          "for a permutation group using a stabilizer chain");

# Note that the last one will always succeed!

##
##  This program is free software: you can redistribute it and/or modify
##  it under the terms of the GNU General Public License as published by
##  the Free Software Foundation, either version 3 of the License, or
##  (at your option) any later version.
##
##  This program is distributed in the hope that it will be useful,
##  but WITHOUT ANY WARRANTY; without even the implied warranty of
##  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
##  GNU General Public License for more details.
##
##  You should have received a copy of the GNU General Public License
##  along with this program.  If not, see <http://www.gnu.org/licenses/>.
##

