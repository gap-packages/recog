#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This files's authors include Max Neunhöffer.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
##
##  Handle the (projective) imprimitive, tensor and tensor-induced cases.
##  This file contains generic methods to find normal subgroups.
##
#############################################################################

BindGlobal( "FINDEVENNORMALOPTS", rec(
  # Try up to this limit random elements to find an involution:
  NonCentInvSearchLimit := 20,
  # Number of odd cases to wait for for computation of involution centraliser:
  NrOddForInvCent := 20,
  # Number of steps after which we give up:
  NrStepsGiveUpForInvCent := 64,
  # Function to determine the order of an element:
  Order := Order,
  # Function to determine equality:
  Eq := EQ,
  # Function to determine whether an element is the identity:
  IsOne := IsOne,
  # Set this to true if you are working with projective groups:
  Projective := false,
  # The random source to use:
  RandomSource := GlobalMersenneTwister,
  # Up to this size we check all involutions:
  SizeLimitAllInvols := 32,
) );

RECOG.RandomSubproduct := function(a,opt)
    local allone,g,isone,prod,rs;

    if IsBound(opt.RandomSource) then
        rs := opt.RandomSource;
    else
        rs := GlobalMersenneTwister;
    fi;
    if IsBound(opt.IsOne) then
        isone := opt.IsOne;
    else
        isone := IsOne;
    fi;

    prod := One(a[1]);
    allone := true;
    repeat
        for g in a do
            if not isone(g) then
                allone := false;
                if Random( rs, [ true, false ] )  then
                    if Random( rs, [ true, false ] )  then
                        prod := prod * g;
                    else
                        prod := g * prod;
                    fi;
                fi;
            fi;
        od;
    until allone or not isone(prod);
    return prod;
end;

RECOG.BlindDescentStep := function(G,x,y,opt)
  # If either x or y are in a proper normal subgroup, then the result will
  # be and it will be nontrivial:
  # Only use for non-abelian groups and for non-trivial x and y!

  local c,i,isone,l,xx;

  if IsBound(opt.IsOne) then
      isone := opt.IsOne;
  else
      isone := IsOne;
  fi;

  c := Comm(x,y);
  if not isone(c) then
      return rec( el := c, Ngens := [c], Nready := false, central := false,
                  isknownproper := false );
  fi;
  # y could be central in G:
  if ForAll(GeneratorsOfGroup(G),g->isone(Comm(g,y))) then
      return rec( el := y, central := true, Ngens := [y], Nready := true,
                  isknownproper := true );  # G was not abelian!
  fi;
  # Now try generators for the normal closure of x:
  l := [x];
  for i in [1..18] do
    xx := RECOG.RandomSubproduct(l,opt)^PseudoRandom(G);
    Add(l,xx);
    c := Comm(xx,y);
    if not isone(c) then
        return rec( el := c, central := false, Ngens := l, Nready := false,
                    isknownproper := false );
    fi;
  od;
  # Now y seems to commute with <x^G> but not with all of G, thus <x^G>
  # is a proper normal subgroup:
  return rec( el := x, central := false, Ngens := l, Nready := true,
              isknownproper := true );
end;

InstallMethod( FindElmOfEvenNormalSubgroup, "for a group object",
  [ IsGroup ],
  function( g ) return FindElmOfEvenNormalSubgroup( g, rec() ); end );

InstallMethod( FindElmOfEvenNormalSubgroup, "for a group object and a record",
  [ IsGroup, IsRecord ],
  function( g, opt )
    local AddList,FindNonCentralInvolution,InvCentDescent,LookAtInvolutions,
          UseElement,abelian,blind,blindr,gens,i,invols,j,pos,res;

    Info(InfoRecog_FindEvenNormal,1,"FindElmOfEvenNormalSubgroup called...");

    # Some helper function:
    AddList := function(l,el)
      if opt.IsOne(el) then
          return false;
      fi;
      for i in [1..Length(l)] do
          if opt.Eq(l[i],el) then
              return false;
          fi;
      od;
      Add(l,el);
      return true;
    end;

    FindNonCentralInvolution := function(h,invols)
      # Find a non-central involution:
      local count,o,x;
      count := 0;
      repeat
          x := PseudoRandom(h);
          o := opt.Order(x);
          if IsEvenInt(o) then
              if InfoLevel(InfoRecog_FindEvenNormal) >= 3 then Print("+\c"); fi;
              x := x^(o/2);
              if AddList(invols,x) then
                  if ForAny(GeneratorsOfGroup(h),a->not opt.Eq(a*x,x*a)) then
                      return x;
                  fi;
              fi;
          else
              if InfoLevel(InfoRecog_FindEvenNormal) >= 3 then Print("-\c"); fi;
          fi;
          count := count + 1;
      until count > opt.NonCentInvSearchLimit;
      return fail;
    end;

    UseElement := function(y)
      # This does a blind descent step possibly ending everything!
      # It refers to the outer variables g, blind, blindr and opt!
      blindr := RECOG.BlindDescentStep(g,blind,y,opt);
      if blindr.isknownproper then
          blindr.success := true;
          if blindr.central then
              blindr.msg := "Found central element";
          else
              blindr.msg := "Normal closure almost certainly proper";
          fi;
      fi;
      blind := blindr.el;
    end;

    InvCentDescent := function(h,x,centinvols)
      local c,centgens,count,counteven,countodd,o,prc,y,z;
      Info(InfoRecog_FindEvenNormal,2,"Descending to involution centraliser...");
      # We produce generators for the involution centraliser:
      centgens := Concatenation([x],centinvols);
      count := 0;
      counteven := 0;
      countodd := 0;

      repeat
          y := PseudoRandom(h);
          c := x * x^y;       # = Comm(x,y) since x is an involution
          o := opt.Order(c);
          if IsEvenInt(o) then   # <x,y> is dihedral with order = 0 mod 4
              if InfoLevel(InfoRecog_FindEvenNormal) >= 3 then Print("+\c"); fi;
              z := c^(o/2);
              if AddList(centinvols,z) then
                  AddList(centgens,z);
                  counteven := counteven + 1;
                  UseElement(z);
                  if blindr.isknownproper then
                      if InfoLevel(InfoRecog_FindEvenNormal)>=3 then Print("\n"); fi;
                      return blindr;
                  fi;
              fi;
              z := (x * x^(y^-1))^(o/2);
              if AddList(centinvols,z) then
                  AddList(centgens,z);
                  counteven := counteven + 1;
                  UseElement(z);
                  if blindr.isknownproper then
                      if InfoLevel(InfoRecog_FindEvenNormal)>=3 then Print("\n"); fi;
                      return blindr;
                  fi;
              fi;
          else
              # This is a uniformly distributed random element in C_G(x):
              if InfoLevel(InfoRecog_FindEvenNormal) >= 3 then Print("-\c"); fi;
              z := y*c^((o-1)/2);
              AddList(centgens,z);
              countodd := countodd + 1;
              o := opt.Order(z);
              if IsEvenInt(o) then
                  z := z^(o/2);
                  if AddList(centinvols,z) then
                      UseElement(z);
                      if blindr.isknownproper then
                      if InfoLevel(InfoRecog_FindEvenNormal)>=3 then Print("\n"); fi;
                          return blindr;
                      fi;
                  fi;
              fi;
          fi;
          count := count + 1;
      until countodd >= opt.NrOddForInvCent or
            count >= opt.NrStepsGiveUpForInvCent;
      if InfoLevel(InfoRecog_FindEvenNormal) >= 3 then Print("\n"); fi;
      c := GroupWithGenerators(centgens);
      prc := ProductReplacer(c,rec( scramblefactor := 3 ) );
      c!.pseudorandomfunc := [rec( func := Next, args := [prc] )];
      return LookAtInvolutions(c,centinvols);
    end;

    LookAtInvolutions := function(h,invols)
      local S,i,invgrp,iter,x,y;
      Info(InfoRecog_FindEvenNormal,2,"Looking for non-central involutions...");
      i := 1;
      while i <= Length(invols) do
          if ForAny(GeneratorsOfGroup(h),
                    a->not opt.Eq(a*invols[i],invols[i]*a)) then
              break;
          fi;
          i := i + 1;
      od;
      if i <= Length(invols) then
          x := invols[i];
          if InfoLevel(InfoRecog_FindEvenNormal) >= 3 then Print("\n"); fi;
      else
          x := FindNonCentralInvolution(h,invols);
          if InfoLevel(InfoRecog_FindEvenNormal) >= 3 then Print("\n"); fi;
          if x = fail then   # suspect that all involutions are central in H!
              Info(InfoRecog_FindEvenNormal,2,"Found ",Length(invols),
                   " central ones.");
              if Length(invols) = 0 then
                  return rec( success := fail,
                              msg := "No central involutions found" );
              fi;
              invgrp := GroupWithGenerators(invols);
              Info(InfoRecog_FindEvenNormal,3,"Computing stabiliser chain...");
              S := StabilizerChain(invgrp,
                         rec( Projective := opt.Projective,
                              IsOne := opt.IsOne,
                              OrbitLengthLimit := 1000,
                              FailInsteadOfError := true ) );
              if IsString(S) then
                  Info(InfoRecog_FindEvenNormal,3,"...failed.");
              else
                  Info(InfoRecog_FindEvenNormal,3,"...done, size is ",Size(S),".");
              fi;
              if not IsString(S) and Size(S) <= opt.SizeLimitAllInvols then
                  iter := GroupIteratorByStabilizerChain(S);
                  Info(InfoRecog_FindEvenNormal,2,"Looking through ",Size(S),
                       " central involutions...");
                  for y in iter do
                      if not opt.IsOne(y) then
                          UseElement(y);
                          if blindr.isknownproper then
                              return blindr;
                          fi;
                      fi;
                  od;
                  blindr.msg :=
  "If at all possible, we found an element of an even proper normal subgroup.";
                  blindr.success := true;
                  return blindr;
              else
                  for i in [1..20] do
                      if IsString(S) then
                          y := RandomSubproduct(invols);
                      else
                          y := Random(S);
                      fi;
                      if not opt.IsOne(y) then
                          UseElement(y);
                          if blindr.isknownproper then
                              return blindr;
                          fi;
                      fi;
                  od;
                  blindr.msg :=
  "We could have found an element of an even proper normal subgroup.";
                  blindr.success := "Perhaps";
                  return blindr;
              fi;
          fi;
          i := Length(invols);
      fi;
      # If we get here, we have found a non-central involution and
      # invols{[1..i-1]} is a list of central ones!
      return InvCentDescent(h,x,invols{[1..i-1]});
  end;

  # Here the main routine starts:

  # Set some defaults:
  if IsBound(opt.Projective) and opt.Projective then
      if not IsBound(opt.IsOne) then opt.IsOne := IsOneProjective; fi;
      if not IsBound(opt.Eq) then opt.Eq := IsEqualProjective; fi;
      if not IsBound(opt.Order) then opt.Order := RECOG.ProjectiveOrder; fi;
  fi;
  GENSS_CopyDefaultOptions( FINDEVENNORMALOPTS, opt );

  # First test whether or not we are abelian:
  if not IsBound(opt.SkipTrivAbelian) then
      gens := GeneratorsOfGroup(g);
      pos := First([1..Length(gens)],i->not opt.IsOne(gens[i]));
      if pos = fail then
          return rec( success := fail, msg := "Group is trivial" );
      fi;
      i := 1;
      abelian := true;
      while abelian and i < Length(gens) do
          j := i+1;
          while abelian and j <= Length(gens) do
              if not opt.Eq(gens[i]*gens[j],gens[j]*gens[i]) then
                  abelian := false;
              fi;
              j := j + 1;
          od;
          i := i + 1;
      od;
      if abelian then
          return rec( success := true, msg := "Group is abelian",
                      el := gens[pos] );
      fi;
  fi;

  # First make sure we have an involution list:
  if IsBound(opt.invols) then
      invols := opt.invols;
  else
      invols := [];
  fi;

  blind := PseudoRandom(g);
  blindr := rec();    # will be overwritten in UseElement
  res := LookAtInvolutions(g,invols);
  Info(InfoRecog_FindEvenNormal,1,"FindElmOfEvenNormalSubgroup: ",res.success,"!");
  return res;
end );

#! @BeginChunk FindElmOfEvenNormal
#! This method looks for a reduction of <A>G</A><M>\le PGL(d,q)</M> in one
#! of the classes D2 (imprimitive), D4 (tensor decomposable) and D7 (tensor
#! induced) of
#! <Cite Key="Neu09" Where="Sections VI.(1.2), VI.(1.4) and VI.(1.7)"/>,
#! variants of the Aschbacher classes C2, C4 and C7. A group in one of these
#! classes has a proper non-scalar normal subgroup <M>N</M>, and the method
#! uses involutions to find an element of it.
#!
#! The search, <C>FindElmOfEvenNormalSubgroup</C>, works modulo scalars. It
#! powers random elements to find an involution <M>x</M> that is not central,
#! replaces <A>G</A> by a subgroup of <M>C_G(x)</M> generated by elements
#! found with the dihedral trick, and repeats until all involutions it finds
#! are central in the current subgroup. Each involution <M>y</M> found on the
#! way drives a blind descent (<C>RECOG.BlindDescentStep</C>): a running
#! element <M>b</M> is replaced by <M>[b,y]</M>, which lies in every normal
#! subgroup containing <M>b</M> or <M>y</M>. The search stops when <M>y</M>
#! is central in <A>G</A>, or when <M>y</M> commutes with <M>b</M> and with
#! random elements of the normal closure of <M>b</M> but not with <A>G</A>,
#! so that this closure is almost certainly proper. If the descent ends
#! first, the central involutions of the last subgroup and their products
#! drive the blind descent too; if none of them stops it, the search returns
#! <M>b</M> anyway.
#!
#! The MeatAxe then tests whether the normal closure <M>N</M> of the element
#! found acts irreducibly; its generators come from the search or from
#! <C>FastNormalClosure</C>. If <M>N</M> acts reducibly,
#! <C>RECOG.SortOutReducibleNormalSubgroup</C> uses the homogeneous
#! components of the natural module restricted to <M>N</M>. If there are
#! several, the image is the permutation action of <A>G</A> on them (D2). If
#! there is one, with constituents of dimension greater than one, a base
#! change writes the elements of <A>G</A> as Kronecker products and hands the
#! image to <Ref Subsect="KroneckerProduct" Style="Text"/> (D4).
#! If <M>N</M> acts irreducibly and <M>d</M> is a proper power, the search is
#! run inside <M>N</M>, and if needed once more inside the subgroup found
#! there, to find a normal subgroup <M>M</M> of <M>N</M>. If <M>M</M> acts
#! reducibly and homogeneously with constituents of dimension <M>e</M> and
#! <M>d=e^k</M>, <C>RECOG.SortOutReducibleSecondNormalSubgroup</C> maps
#! <A>G</A> to its permutation action on the <M>k</M> conjugates of <M>M</M>,
#! which are the direct factors of <M>N</M> (D7).
#!
#! The method returns <K>Success</K> or <K>TemporaryFailure</K>, never
#! <K>NeverApplicable</K>. It fails temporarily if the search finds no
#! involution, if <M>N</M> acts irreducibly and <M>d</M> is not a proper
#! power, if <M>M</M> acts irreducibly, or if the subgroups found yield none
#! of the reductions above.
#! @EndChunk
BindRecogMethod("FindHomMethodsProjective", "FindElmOfEvenNormal",
"find D2, D4 or D7 by finding an element of an even normal subgroup",
function(ri)
  local G,cf,count,f,m,mm,r,res,rr;
  G := Grp(ri);
  RECOG.SetPseudoRandomStamp(G,"FindElmOfEvenNormal");
  r := FindElmOfEvenNormalSubgroup(G,
          rec( Projective := true, SkipTrivAbelian := true ));
  if r.success = fail then
      return TemporaryFailure; # FIXME: TemporaryFailure here really correct?
  fi;
  if not IsBound(r.Nready) or not r.Nready then
      r.Ngens := FastNormalClosure(G,[r.el],20);
  fi;
  f := ri!.field;
  m := GModuleByMats(r.Ngens,f);
  if not MTX.IsIrreducible(m) then
      Info(InfoRecog,2,
           "FindElmOfEvenNormal: Found reducible proper normal subgroup!");
      return RECOG.SortOutReducibleNormalSubgroup(ri,G,r.Ngens,m);
  else
      Info(InfoRecog,2,
           "FindElmOfEvenNormal: Could be irreducible proper normal subgroup!");
      # First find out whether or not the dimension is a proper power:
      cf := RECOG.IsPower(ri!.dimension);
      if Length(cf) = 0 then
          Info(InfoRecog,2,"Dimension no proper power, so this is not D7.");
      else
          count := 0;
          repeat
              count := count + 1;
              rr := FindElmOfEvenNormalSubgroup(Group(r.Ngens),
                           rec( Projective:=true, SkipTrivAbelian := true ));
              if rr.success = fail then continue; fi;
              if not IsBound(rr.Nready) or not rr.Nready then
                  rr.Ngens := FastNormalClosure(r.Ngens,[rr.el],20);
              fi;
              mm := GModuleByMats(rr.Ngens,f);
              if MTX.IsIrreducible(mm) then
                  Info(InfoRecog,2,
           "FindElmOfEvenNormal: Second normal subgroup was not reducible.");
                  return TemporaryFailure; # FIXME: TemporaryFailure here really correct?
              fi;
              res := RECOG.SortOutReducibleSecondNormalSubgroup(
                                      ri,G,rr.Ngens,mm);
              if res = Success then
                  return Success;
              fi;
              r := rr;
          until count >= 2;
      fi;
  fi;
  return TemporaryFailure; # FIXME: TemporaryFailure here really correct?
end);
