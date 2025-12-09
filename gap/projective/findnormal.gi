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
  # Number of random elements for normal closure computation:
  NrGensNormalClosure := 10,
  # Number of odd cases to wait for for computation of involution centraliser:
  NrOddForInvCent := 20,
  # Number of steps after which we give up:
  NrStepsGiveUpForInvCent := 64,
  # Number of random elements to use for GuessProperness:
  NrElsGuessProperness := 20,
  # Number of random elements of G to look at orders:
  NrElsLookAtOrders := 5,
  # Function to determine the order of an element:
  Order := Order,
  # Function to determine equality:
  Eq := EQ,
  # Function to determine whether an element is the identity:
  IsOne := IsOne,
  # Set this to true if you are working with projective groups:
  Projective := false,
  # Set this to true if blind descent should be tried:
  DoBlindDescent := false,
  # The random source to use:
  RandomSource := GlobalMersenneTwister,
  # Up to this size we check all involutions:
  SizeLimitAllInvols := 32,
) );

# InstallGlobalFunction( RECOG_IsNormal,
#   function(g,h,projective)
#     local S,x,y;
#     if HasStoredStabilizerChain(h) and not projective then
#         S := StoredStabilizerChain(h);
#     else
#         S := StabilizerChain(h,rec( Projective := projective ));
#     fi;
#     for x in GeneratorsOfGroup(g) do
#         for y in GeneratorsOfGroup(h) do
#             if not y^x in S then return false; fi;
#         od;
#     od;
#     return true;
#   end );
# 
# InstallMethod( FindEvenNormalSubgroup, "for a group object",
#   [ IsGroup ],
#   function( g ) return FindEvenNormalSubgroup( g, rec() ); end );
# 
# InstallMethod( FindEvenNormalSubgroup, "for a group object and a record",
#   [ IsGroup, IsRecord ],
#   function( g, opt )
#     local AddList,FindNonCentralInvolution,GuessProperness,InvCentDescent,
#           LookAtInvolutions,NormalClosure,TestElement,ggens,ggenso,i,res;
# 
#     Info(InfoFindEvenNormal,1,"FindEvenNormalSubgroup called...");
# 
#     # Some helper function:
#     AddList := function(l,el)
#       if opt.IsOne(el) then return false; fi;
#       for i in [1..Length(l)] do
#           if opt.Eq(l[i],el) then return false; fi;
#       od;
#       Add(l,el);
#       return true;
#     end;
# 
#     FindNonCentralInvolution := function(gens,pr,invols)
#       local count,o,x;
#       if pr = false then
#           pr := ProductReplacer(gens, rec( scramblefactor := 3 ) );
#       fi;
#       # Find a non-central involution:
#       count := 0;
#       repeat
#           x := Next(pr);
#           o := opt.Order(x);
#           if IsEvenInt(o) then
#               if InfoLevel(InfoFindEvenNormal) >= 3 then Print("+\c"); fi;
#               x := x^(o/2);
#               if AddList(invols,x) then
#                   if ForAny(gens,a->not opt.Eq(a*x,x*a)) then
#                       return x;
#                   fi;
#               fi;
#           else
#               if InfoLevel(InfoFindEvenNormal) >= 3 then Print("-\c"); fi;
#           fi;
#           count := count + 1;
#       until count > opt.NonCentInvSearchLimit;
#       return fail;
#     end;
# 
#     NormalClosure := function(prg,Ngens)
#       local i,l,pr;
#       pr := ProductReplacer(Ngens,rec( normalin := prg,
#                                        scramble := 20,
#                                        scramblefactor := 2,
#                                        addslots := 10 ));
#       l := ShallowCopy(Ngens);
#       for i in [1..opt.NrGensNormalClosure] do
#           if InfoLevel(InfoFindEvenNormal) >= 3 then Print("N\c"); fi;
#           AddList(l,Next(pr));
#       od;
#       return rec( Ngens := l, prN := pr, count := opt.NrGensNormalClosure );
#     end;
# 
#     GuessProperness := function( Ngens, prN )
#       # Ngens: generators for N (will be extended)
#       # prN: product replacer producing elements in normal closure
#       local a,i,j,o,stage;
#       o := ShallowCopy(ggenso);
#       for i in [1..Length(Ngens)] do
#           if InfoLevel(InfoFindEvenNormal) >= 3 then Print("G\c"); fi;
#           a := Ngens[i];
#           for j in [1..Length(ggens)] do
#               if o[j] <> 1 then
#                   o[j] := GcdInt(o[j],opt.Order(a*ggens[j]));
#               fi;
#           od;
#           if ForAll(o,k->k = 1) then return false; fi;
#       od;
#       stage := 0;
#       repeat
#           stage := stage + 1;
#           if InfoLevel(InfoFindEvenNormal) >= 3 then Print(stage,"\c"); fi;
#           for i in [1..opt.NrElsGuessProperness] do
#               if InfoLevel(InfoFindEvenNormal) >= 3 then Print("G\c"); fi;
#               a := Next(prN);
#               if AddList(Ngens,a) then
#                   for j in [1..Length(ggens)] do
#                       if o[j] <> 1 then
#                           o[j] := GcdInt(o[j],opt.Order(a*ggens[j]));
#                       fi;
#                   od;
#                   if ForAll(o,k->k = 1) then return false; fi;
#               fi;
#           od;
#       until Number(o,k->k = 1) <= QuoInt(Length(o),2) or stage >= 3;
#       return o;
#     end;
# 
#     TestElement := function(x)
#       local orderests,r;
#       Info(InfoFindEvenNormal,2,"Testing element...");
#       r := NormalClosure(opt.pr,[x]);
#       orderests := GuessProperness(r.Ngens,r.prN);
#       if InfoLevel(InfoFindEvenNormal) >= 3 then Print("\n"); fi;
#       Info(InfoFindEvenNormal,2,"Order estimates: ",orderests);
#       if orderests <> false then
#           return rec( success := true, orderests := orderests,
#                       Ngens := r.Ngens, prN := r.prN, x := x,
#                       msg := "Ngens should generate a proper normal subgroup" );
#       else
#           return fail;
#       fi;
#     end;
# 
#     InvCentDescent := function(hgens,prh,x,centinvols)
#       local blind,c,centgens,count,counteven,countodd,o,prc,r,w,y,z;
#       Info(InfoFindEvenNormal,2,"Descending to involution centraliser...");
#       # We produce generators for the involution centraliser:
#       centgens := Concatenation([x],centinvols);
#       count := 0;
#       counteven := 0;
#       countodd := 0;
#       blind := false;
#       repeat
#           y := Next(prh);
#           c := x * x^y;       # = Comm(x,y) since x is an involution
#           o := opt.Order(c);
#           if IsEvenInt(o) then   # <x,y> is dihedral with order = 0 mod 4
#               if InfoLevel(InfoFindEvenNormal) >= 3 then Print("+\c"); fi;
#               z := c^(o/2);
#               if AddList(centinvols,z) then
#                   AddList(centgens,z);
#                   counteven := counteven + 1;
#                   if opt.DoBlindDescent then
#                       if blind = false then
#                           blind := z;
#                       else
#                           w := blind^-1*z*blind*z;   # = Comm(blind,z)
#                           if not opt.IsOne(w) then
#                               blind := w;
#                           fi;
#                       fi;
#                   fi;
#               fi;
#           else
#               # This is a uniformly distributed random element in C_G(x):
#               if InfoLevel(InfoFindEvenNormal) >= 3 then Print("-\c"); fi;
#               z := y*c^((o-1)/2);
#               AddList(centgens,z);
#               countodd := countodd + 1;
#               o := opt.Order(z);
#               if IsEvenInt(o) then
#                   if AddList(centinvols,z^(o/2)) then
#                       if opt.DoBlindDescent then
#                           if blind = false then
#                               blind := z;
#                           else
#                               w := blind^-1*z*blind*z;   # = Comm(blind,z)
#                               if not opt.IsOne(w) then
#                                   blind := w;
#                               fi;
#                           fi;
#                       fi;
#                   fi;
#               fi;
#           fi;
#           count := count + 1;
#       until countodd >= opt.NrOddForInvCent or
#             count >= opt.NrStepsGiveUpForInvCent;
#       if InfoLevel(InfoFindEvenNormal) >= 3 then Print("\n"); fi;
#       if opt.DoBlindDescent and blind <> false then
#           r := TestElement(blind);
#           if r <> fail then return r; fi;
#       fi;
#       prc := ProductReplacer(centgens,rec( scramblefactor := 3 ) );
#       return LookAtInvolutions(centgens,prc,centinvols);
#     end;
# 
#     LookAtInvolutions := function(hgens,prh,invols)
#       local S,i,invgrp,iter,pr,r,x,y;
#       Info(InfoFindEvenNormal,2,"Looking for non-central involutions...");
#       i := 1;
#       while i <= Length(invols) do
#           if ForAny(hgens,a->not opt.Eq(a*invols[i],invols[i]*a)) then
#               break;
#           fi;
#           i := i + 1;
#       od;
#       if i <= Length(invols) then
#           x := invols[i];
#           if InfoLevel(InfoFindEvenNormal) >= 3 then Print("\n"); fi;
#       else
#           x := FindNonCentralInvolution(hgens,prh,invols);
#           if InfoLevel(InfoFindEvenNormal) >= 3 then Print("\n"); fi;
#           if x = fail then   # suspect that all involutions are central in H!
#               Info(InfoFindEvenNormal,2,"Found ",Length(invols),
#                    " central ones.");
#               if Length(invols) = 0 then
#                   return rec( success := false,
#                               msg := "No central involutions found" );
#               fi;
#               invgrp := Group(invols);
#               S := StabilizerChain(invgrp,rec( Projective := opt.Projective,
#                                                isone := opt.IsOne ) );
#               if Size(S) <= opt.SizeLimitAllInvols then
#                   iter := GroupIteratorByStabilizerChain(S);
#                   Info(InfoFindEvenNormal,2,"Looking through ",Size(S),
#                        " central involutions...");
#                   for y in iter do
#                       if not opt.IsOne(y) then
#                           r := TestElement(y);
#                           if r <> fail then return r; fi;
#                       fi;
#                   od;
#                   return rec( success := false,
#                      msg := "No central involution found normal subgroup" );
#               else
#                   for i in [1..20] do
#                       y := Random(S);
#                       if not opt.IsOne(y) then
#                           r := TestElement(y);
#                           if r <> fail then return r; fi;
#                       fi;
#                   od;
#                   return rec( success := false,
#                      msg := Concatenation("20 out of ",String(Size(S)),
#                                           " random central involutions did ",
#                                           "not find a normal subgroup") );
#               fi;
#           fi;
#           i := Length(invols);
#       fi;
#       # If we get here, we have found a non-central involution and
#       # invols{[1..i-1]} is a list of central ones!
#       return InvCentDescent(hgens,prh,x,invols{[1..i-1]});
#   end;
# 
#   # Here the main routine starts:
# 
#   # Set some defaults:
#   if IsBound(opt.Projective) and opt.Projective then
#       if not IsBound(opt.IsOne) then opt.IsOne := IsOneProjective; fi;
#       if not IsBound(opt.Eq) then opt.Eq := IsEqualProjective; fi;
#       if not IsBound(opt.Order) then opt.Order := RECOG.ProjectiveOrder; fi;
#   fi;
#   GENSS_CopyDefaultOptions( FINDEVENNORMALOPTS, opt );
# 
#   # Initialise a product replacer:
#   if not IsBound(opt.pr) then
#       opt.pr := ProductReplacer(GeneratorsOfGroup(g));
#   fi;
# 
#   # First make sure we have an involution list:
#   if not IsBound(opt.invols) then
#       opt.invols := [];
#   fi;
# 
#   # Some more preparations:
#   ggens := EmptyPlist(opt.NrElsLookAtOrders);
#   for i in [1..opt.NrElsLookAtOrders] do
#       Add(ggens,Next(opt.pr));
#   od;
#   ggenso := List(ggens,opt.Order);
# 
#   res := LookAtInvolutions(GeneratorsOfGroup(g),opt.pr,opt.invols);
#   if IsRecord(res) and res.success then
#       Info(InfoFindEvenNormal,1,"FindEvenNormalSubgroup:  SUCCESS!");
#   else
#       Info(InfoFindEvenNormal,1,"FindEvenNormalSubgroup:  FAILURE!");
#   fi;
#   return res;
# end );

# All powers that can be done with at most 5 multiplications/inversion:
RECOG.MYRANDOMSUBPRODUCTPOWERS :=
  [1,2,3,4,5,6,7,8,9,10,11,12,13,14,16,17,18,20,24,32,
   -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-12,-16];
  # (without undue and unimplemented tricks)!

RECOG.RandomSubproduct := function(a,opt)
    local allone,dopowers,g,isone,power,prod,rs;

    if IsBound(opt.RandomSource) then
        rs := opt.RandomSource;
    else
        rs := GlobalMersenneTwister;
    fi;
    if IsBound(opt.DoPowers) then
        dopowers := opt.DoPowers;
    else
        dopowers := false;
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
                    if dopowers then
                        power := Random(rs,RECOG.RANDOMSUBPRODUCTPOWERS);
                    else
                        power := 1;
                    fi;
                    if Random( rs, [ true, false ] )  then
                        prod := prod * g^power;
                    else
                        prod := g^power * prod;
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

  local c,i,isone,l,usepseudo,xx;

  if IsBound(opt.IsOne) then
      isone := opt.IsOne;
  else
      isone := IsOne;
  fi;
  if IsBound(opt.UsePseudoRandom) then
      usepseudo := opt.UsePseudoRandom;
  else
      usepseudo := false;
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
    if usepseudo then
        xx := RECOG.RandomSubproduct(l,opt)^PseudoRandom(G);
    else
        xx := RECOG.RandomSubproduct(l,opt)^
              RECOG.RandomSubproduct(GeneratorsOfGroup(G),opt);
    fi;
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

    Info(InfoFindEvenNormal,1,"FindElmOfEvenNormalSubgroup called...");

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
              if InfoLevel(InfoFindEvenNormal) >= 3 then Print("+\c"); fi;
              x := x^(o/2);
              if AddList(invols,x) then
                  if ForAny(GeneratorsOfGroup(h),a->not opt.Eq(a*x,x*a)) then
                      return x;
                  fi;
              fi;
          else
              if InfoLevel(InfoFindEvenNormal) >= 3 then Print("-\c"); fi;
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
      Info(InfoFindEvenNormal,2,"Descending to involution centraliser...");
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
              if InfoLevel(InfoFindEvenNormal) >= 3 then Print("+\c"); fi;
              z := c^(o/2);
              if AddList(centinvols,z) then
                  AddList(centgens,z);
                  counteven := counteven + 1;
                  UseElement(z);
                  if blindr.isknownproper then
                      if InfoLevel(InfoFindEvenNormal)>=3 then Print("\n"); fi;
                      return blindr;
                  fi;
              fi;
              z := (x * x^(y^-1))^(o/2);
              if AddList(centinvols,z) then
                  AddList(centgens,z);
                  counteven := counteven + 1;
                  UseElement(z);
                  if blindr.isknownproper then
                      if InfoLevel(InfoFindEvenNormal)>=3 then Print("\n"); fi;
                      return blindr;
                  fi;
              fi;
          else
              # This is a uniformly distributed random element in C_G(x):
              if InfoLevel(InfoFindEvenNormal) >= 3 then Print("-\c"); fi;
              z := y*c^((o-1)/2);
              AddList(centgens,z);
              countodd := countodd + 1;
              o := opt.Order(z);
              if IsEvenInt(o) then
                  z := z^(o/2);
                  if AddList(centinvols,z^(o/2)) then
                      UseElement(z);
                      if blindr.isknownproper then
                      if InfoLevel(InfoFindEvenNormal)>=3 then Print("\n"); fi;
                          return blindr;
                      fi;
                  fi;
              fi;
          fi;
          count := count + 1;
      until countodd >= opt.NrOddForInvCent or
            count >= opt.NrStepsGiveUpForInvCent;
      if InfoLevel(InfoFindEvenNormal) >= 3 then Print("\n"); fi;
      c := GroupWithGenerators(centgens);
      prc := ProductReplacer(c,rec( scramblefactor := 3 ) );
      c!.pseudorandomfunc := [rec( func := Next, args := [prc] )];
      return LookAtInvolutions(c,centinvols);
    end;

    LookAtInvolutions := function(h,invols)
      local S,i,invgrp,iter,x,y;
      Info(InfoFindEvenNormal,2,"Looking for non-central involutions...");
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
          if InfoLevel(InfoFindEvenNormal) >= 3 then Print("\n"); fi;
      else
          x := FindNonCentralInvolution(h,invols);
          if InfoLevel(InfoFindEvenNormal) >= 3 then Print("\n"); fi;
          if x = fail then   # suspect that all involutions are central in H!
              Info(InfoFindEvenNormal,2,"Found ",Length(invols),
                   " central ones.");
              if Length(invols) = 0 then
                  return rec( success := fail,
                              msg := "No central involutions found" );
              fi;
              invgrp := GroupWithGenerators(invols);
              Info(InfoFindEvenNormal,3,"Computing stabiliser chain...");
              S := StabilizerChain(invgrp,
                         rec( Projective := opt.Projective,
                              IsOne := opt.IsOne,
                              OrbitLengthLimit := 1000,
                              FailInsteadOfError := true ) );
              if IsString(S) then
                  Info(InfoFindEvenNormal,3,"...failed.");
              else
                  Info(InfoFindEvenNormal,3,"...done, size is ",Size(S),".");
              fi;
              if not IsString(S) and Size(S) <= opt.SizeLimitAllInvols then
                  iter := GroupIteratorByStabilizerChain(S);
                  Info(InfoFindEvenNormal,2,"Looking through ",Size(S),
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
          res := rec( success := fail, msg := "Group is trivial" );
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
          res := rec( success := true, msg := "Group is abelian",
                      el := gens[pos] );
      fi;
  fi;

  opt.UsePseudoRandom := true;   # This is for the blind descent

  # First make sure we have an involution list:
  if IsBound(opt.invols) then
      invols := opt.invols;
  else
      invols := [];
  fi;

  blind := PseudoRandom(g);
  blindr := rec();    # will be overwritten in UseElement
  res := LookAtInvolutions(g,invols);
  Info(InfoFindEvenNormal,1,"FindElmOfEvenNormalSubgroup: ",res.success,"!");
  return res;
end );

# FindHomMethodsProjective.FindEvenNormal := function(ri,G)
#   local count,r,rr,f,m,mm,res;
#   r := FindEvenNormalSubgroup(G,
#           rec( Projective := true, DoBlindDescent := true));
#   if r.success then
#       f := ri!.field;
#       m := GModuleByMats(r.Ngens,f);
#       if not MTX.IsIrreducible(m) then
#           Info(InfoRecog,2,
#                "FindEvenNormal: Found reducible proper normal subgroup!");
#           return RECOG.SortOutReducibleNormalSubgroup(ri,G,r.Ngens,m);
#       else
#           Info(InfoRecog,2,
#                "FindEvenNormal: Found irreducible proper normal subgroup!");
#           count := 0;
#           repeat
#               count := count + 1;
#               rr := FindEvenNormalSubgroup(Group(r.Ngens),
#                            rec( Projective:=true, DoBlindDescent := true ));
#               if rr.success then
#                   mm := GModuleByMats(rr.Ngens,f);
#                   if MTX.IsIrreducible(mm) then
#                       Info(InfoRecog,2,
#             "FindEvenNormal: Second normal subgroup was not reducible.");
#                       return fail; # FIXME: fail = TemporaryFailure here really correct?
#                   fi;
#                   res := RECOG.SortOutReducibleSecondNormalSubgroup(ri,G,
#                                     rr.Ngens,mm);
#                   if res = true then return Success; fi;
#                   r := rr;
#               else
#                   return fail; # FIXME: fail = TemporaryFailure here really correct?
#               fi;
#           until count >= 2;
#       fi;
#   fi;
#   return fail; # FIXME: fail = TemporaryFailure here really correct?
# end;

#! @BeginChunk FindElmOfEvenNormal
#! TODO
#! @EndChunk
BindRecogMethod(FindHomMethodsProjective, "FindElmOfEvenNormal",
"find D2, D4 or D7 by finding an element of an even normal subgroup",
function(ri,G)
  local cf,count,f,m,mm,r,res,rr;
  RECOG.SetPseudoRandomStamp(G,"FindElmOfEvenNormal");
  r := FindElmOfEvenNormalSubgroup(G,
          rec( Projective := true, SkipTrivAbelian := true ));
  if r.success = fail then # FIXME: fail = TemporaryFailure here really correct?
      return fail; # FIXME: fail = TemporaryFailure here really correct?
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
                  return fail; # FIXME: fail = TemporaryFailure here really correct?
              fi;
              res := RECOG.SortOutReducibleSecondNormalSubgroup(
                                      ri,G,rr.Ngens,mm);
              if res = true then
                  return Success;
              fi;
              r := rr;
          until count >= 2;
      fi;
  fi;
  return fail; # FIXME: fail = TemporaryFailure here really correct?
end);
