#############################################################################
##
##  findnormal.gi          
##                                recog package  
##                                                        Max Neunhoeffer
##
##  Copyright 2009 by the authors.
##  This file is free software, see license information at the end.
##
##  Handle the (projective) imprimitive, tensor and tensor-induced cases.
##  This file contains generic methods to find normal subgroups.
##
#############################################################################

InstallValue( FINDEVENNORMALOPTS, rec(
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
) );

InstallGlobalFunction( RECOG_EqProjective,
  function(a,b)
    local i,p,s;
    p := PositionNonZero(a[1]);
    s := b[1][p] / a[1][p];
    for i in [1..Length(a)] do
        if s*a[i] <> b[i] then return false; fi;
    od;
    return true;
  end );

InstallGlobalFunction( RECOG_IsNormal,
  function(g,h,projective)
    local S,x,y;
    if HasStoredStabilizerChain(h) and not(projective) then
        S := StoredStabilizerChain(h);
    else
        S := StabilizerChain(h,rec( Projective := projective ));
    fi;
    for x in GeneratorsOfGroup(g) do
        for y in GeneratorsOfGroup(h) do
            if not(y^x in S) then return false; fi;
        od;
    od;
    return true;
  end );

InstallMethod( FindEvenNormalSubgroup, "for a group object",
  [ IsGroup ],
  function( g ) return FindEvenNormalSubgroup( g, rec() ); end );

InstallMethod( FindEvenNormalSubgroup, "for a group object and a record",
  [ IsGroup, IsRecord ],
  function( g, opt )
    local AddList,FindNonCentralInvolution,GuessProperness,InvCentDescent,
          LookAtInvolutions,NormalClosure,TestElement,ggens,ggenso,i,res;

    Info(InfoFindEvenNormal,1,"FindEvenNormalSubgroup called...");

    # Some helper function:
    AddList := function(l,el)
      if opt.IsOne(el) then return false; fi;
      for i in [1..Length(l)] do
          if opt.Eq(l[i],el) then return false; fi;
      od;
      Add(l,el);
      return true;
    end;

    FindNonCentralInvolution := function(gens,pr,invols)
      local count,o,x;
      if pr = false then
          pr := ProductReplacer(gens, rec( scramblefactor := 3 ) );
      fi;
      # Find a non-central involution:
      count := 0;
      repeat
          x := Next(pr);
          o := opt.Order(x);
          if IsEvenInt(o) then
              if InfoLevel(InfoFindEvenNormal) >= 3 then Print("+\c"); fi;
              x := x^(o/2);
              if AddList(invols,x) then
                  if ForAny(gens,a->not opt.Eq(a*x,x*a)) then
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

    NormalClosure := function(prg,Ngens)
      local i,l,pr;
      pr := ProductReplacer(Ngens,rec( normalin := prg,
                                       scramble := 20,
                                       scramblefactor := 2,
                                       addslots := 10 ));
      l := ShallowCopy(Ngens);
      for i in [1..opt.NrGensNormalClosure] do
          if InfoLevel(InfoFindEvenNormal) >= 3 then Print("N\c"); fi;
          AddList(l,Next(pr));
      od;
      return rec( Ngens := l, prN := pr, count := opt.NrGensNormalClosure );
    end;

    GuessProperness := function( Ngens, prN )
      # Ngens: generators for N (will be extended)
      # prN: product replacer producing elements in normal closure
      local a,i,j,o,stage;
      o := ShallowCopy(ggenso);
      for i in [1..Length(Ngens)] do
          if InfoLevel(InfoFindEvenNormal) >= 3 then Print("G\c"); fi;
          a := Ngens[i];
          for j in [1..Length(ggens)] do
              if o[j] <> 1 then
                  o[j] := GcdInt(o[j],opt.Order(a*ggens[j]));
              fi;
          od;
          if ForAll(o,k->k = 1) then return false; fi;
      od;
      stage := 0;
      repeat
          stage := stage + 1;
          if InfoLevel(InfoFindEvenNormal) >= 3 then Print(stage,"\c"); fi;
          for i in [1..opt.NrElsGuessProperness] do
              if InfoLevel(InfoFindEvenNormal) >= 3 then Print("G\c"); fi;
              a := Next(prN);
              if AddList(Ngens,a) then
                  for j in [1..Length(ggens)] do
                      if o[j] <> 1 then
                          o[j] := GcdInt(o[j],opt.Order(a*ggens[j]));
                      fi;
                  od;
                  if ForAll(o,k->k = 1) then return false; fi;
              fi;
          od;
      until Number(o,k->k = 1) <= QuoInt(Length(o),2) or stage >= 3;
      return o;
    end;

    TestElement := function(x)
      local orderests,r;
      Info(InfoFindEvenNormal,2,"Testing element...");
      r := NormalClosure(opt.pr,[x]);
      orderests := GuessProperness(r.Ngens,r.prN);
      if InfoLevel(InfoFindEvenNormal) >= 3 then Print("\n"); fi;
      Info(InfoFindEvenNormal,2,"Order estimates: ",orderests);
      if orderests <> false then
          return rec( success := true, orderests := orderests,
                      Ngens := r.Ngens, prN := r.prN, x := x,
                      msg := "Ngens should generate a proper normal subgroup" );
      else
          return fail;
      fi;
    end;

    InvCentDescent := function(hgens,prh,x,centinvols)
      local blind,c,centgens,count,counteven,countodd,o,prc,r,w,y,z;
      Info(InfoFindEvenNormal,2,"Descending to involution centraliser...");
      # We produce generators for the involution centraliser:
      centgens := Concatenation([x],centinvols);
      count := 0;
      counteven := 0;
      countodd := 0;
      blind := false;
      repeat
          y := Next(prh);
          c := x * x^y;       # = Comm(x,y) since x is an involution
          o := opt.Order(c);
          if IsEvenInt(o) then   # <x,y> is dihedral with order = 0 mod 4
              if InfoLevel(InfoFindEvenNormal) >= 3 then Print("+\c"); fi;
              z := c^(o/2);
              if AddList(centinvols,z) then
                  AddList(centgens,z);
                  counteven := counteven + 1;
                  if opt.DoBlindDescent then
                      if blind = false then
                          blind := z;
                      else
                          w := blind^-1*z*blind*z;   # = Comm(blind,z)
                          if not(opt.IsOne(w)) then
                              blind := w;
                          fi;
                      fi;
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
                  if AddList(centinvols,z^(o/2)) then
                      if opt.DoBlindDescent then
                          if blind = false then
                              blind := z;
                          else
                              w := blind^-1*z*blind*z;   # = Comm(blind,z)
                              if not(opt.IsOne(w)) then
                                  blind := w;
                              fi;
                          fi;
                      fi;
                  fi;
              fi;
          fi;
          count := count + 1;
      until countodd >= opt.NrOddForInvCent or
            count >= opt.NrStepsGiveUpForInvCent;
      if InfoLevel(InfoFindEvenNormal) >= 3 then Print("\n"); fi;
      if opt.DoBlindDescent and blind <> false then
          r := TestElement(blind);
          if r <> fail then return r; fi;
      fi;
      prc := ProductReplacer(centgens,rec( scramblefactor := 3 ) );
      return LookAtInvolutions(centgens,prc,centinvols);
    end;

    LookAtInvolutions := function(hgens,prh,invols)
      local S,i,invgrp,iter,pr,r,x,y;
      Info(InfoFindEvenNormal,2,"Looking for non-central involutions...");
      i := 1;
      while i <= Length(invols) do
          if ForAny(hgens,a->not opt.Eq(a*invols[i],invols[i]*a)) then
              break;
          fi;
          i := i + 1;
      od;
      if i <= Length(invols) then
          x := invols[i];
          if InfoLevel(InfoFindEvenNormal) >= 3 then Print("\n"); fi;
      else
          x := FindNonCentralInvolution(hgens,prh,invols);
          if InfoLevel(InfoFindEvenNormal) >= 3 then Print("\n"); fi;
          if x = fail then   # suspect that all involutions are central in H!
              Info(InfoFindEvenNormal,2,"Found ",Length(invols),
                   " central ones.");
              if Length(invols) = 0 then
                  return rec( success := false,
                              msg := "No central involutions found" );
              fi;
              invgrp := Group(invols);
              S := StabilizerChain(invgrp,rec( Projective := opt.Projective,
                                               isone := opt.IsOne ) );
              if Size(S) <= 32 then
                  iter := GroupIteratorByStabilizerChain(S);
                  Info(InfoFindEvenNormal,2,"Looking through ",Size(S),
                       " central involutions...");
                  for y in iter do
                      if not(opt.IsOne(y)) then
                          r := TestElement(y);
                          if r <> fail then return r; fi;
                      fi;
                  od;
                  return rec( success := false,
                     msg := "No central involution found normal subgroup" );
              else
                  for i in [1..20] do
                      y := Random(S);
                      if not(opt.IsOne(y)) then
                          r := TestElement(y);
                          if r <> fail then return r; fi;
                      fi;
                  od;
                  return rec( success := false,
                     msg := Concatenation("20 out of ",String(Size(S)),
                                          " random central involutions did ",
                                          "not find a normal subgroup") );
              fi;
          fi;
          i := Length(invols);
      fi;
      # If we get here, we have found a non-central involution and
      # invols{[1..i-1]} is a list of central ones!
      return InvCentDescent(hgens,prh,x,invols{[1..i-1]});
  end;

  # Here the main routine starts:

  # Set some defaults:
  if IsBound(opt.Projective) and opt.Projective then
      if not(IsBound(opt.IsOne)) then opt.IsOne := GENSS_IsOneProjective; fi;
      if not(IsBound(opt.Eq)) then opt.Eq := RECOG_EqProjective; fi;
      if not(IsBound(opt.Order)) then opt.Order := RECOG.ProjectiveOrder; fi;
  fi;
  GENSS_CopyDefaultOptions( FINDEVENNORMALOPTS, opt );

  # Initialise a product replacer:
  if not(IsBound(opt.pr)) then
      opt.pr := ProductReplacer(GeneratorsOfGroup(g));
  fi;

  # First make sure we have an involution list:
  if not(IsBound(opt.invols)) then
      opt.invols := [];
  fi;

  # Some more preparations:
  ggens := EmptyPlist(opt.NrElsLookAtOrders);
  for i in [1..opt.NrElsLookAtOrders] do
      Add(ggens,Next(opt.pr));
  od;
  ggenso := List(ggens,opt.Order);

  res := LookAtInvolutions(GeneratorsOfGroup(g),opt.pr,opt.invols);
  if IsRecord(res) and res.success then
      Info(InfoFindEvenNormal,1,"FindEvenNormalSubgroup:  SUCCESS!");
  else
      Info(InfoFindEvenNormal,1,"FindEvenNormalSubgroup:  FAILURE!");
  fi;
  return res;
end );

FindHomMethodsProjective.FindEvenNormal := function(ri,G)
  local count,r,rr,f,m,mm,res;
  r := FindEvenNormalSubgroup(G,
          rec( Projective := true, DoBlindDescent := true));
  if r.success then
      f := FieldOfMatrixGroup(G);
      m := GModuleByMats(r.Ngens,f);
      if not(MTX.IsIrreducible(m)) then
          Info(InfoRecog,2,"Found reducible proper normal subgroup!");
          return RECOG.SortOutReducibleNormalSubgroup(ri,G,r.Ngens,m);
      else
          Info(InfoRecog,2,"Found irreducible proper normal subgroup!");
          count := 0;
          repeat
              count := count + 1;
              rr := FindEvenNormalSubgroup(Group(r.Ngens),
                           rec( Projective:=true, DoBlindDescent := true ));
              if rr.success then
                  mm := GModuleByMats(rr.Ngens,f);
                  if MTX.IsIrreducible(mm) then 
                      Info(InfoRecog,2,
                           "Second normal subgroup was not reducible.");
                      return fail; 
                  fi;
                  res := RECOG.SortOutReducibleSecondNormalSubgroup(ri,G,
                                    rr.Ngens,mm);
                  if res = true then return res; fi;
                  r := rr;
              else
                  return fail;
              fi;
          until count >= 2;
      fi;
  fi;
  return fail;
end;

