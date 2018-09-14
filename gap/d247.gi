#############################################################################
##
##  d247.gi
##                                recog package
##                                                        Max Neunhoeffer
##
##  Copyright 2006-2008 by the authors.
##  This file is free software, see license information at the end.
##
##  Handle the (projective) imprimitive, tensor and tensor-induced cases.
##
##  This implementation is inspired by Max Neunhoeffer's habil thesis
##  and the variations D2, D4 and D7 of the Aschbacher cases. A copy can
##  be obtained via Frank Luebeck, LDfM RWTH Aachen.
##
#############################################################################

RECOG.InvolutionSearcher := function(pr,ord,tol)
  # pr a product replacer
  # ord a function computing the order
  # tol the number of tries
  local count,o,x;
  count := 0;
  repeat
      count := count + 1;
      x := Next(pr);
      o := ord(x);
      if IsEvenInt(o) then
          return x^(o/2);
      fi;
  until count > tol;
  return fail;
end;

RECOG.CentralisingElementOfInvolution := function(pr,ord,x)
  # x an involution in G
  local o,r,y,z;
  r := Next(pr);
  y := x^r;
  # Now x and y generate a dihedral group
  if x=y then return r; fi;
  z := x*y;
  o := ord(z);
  if IsEvenInt(o) then
      return z^(o/2);
  else
      return z^((o+1)/2)*r^(-1);
  fi;
end;

RECOG.InvolutionCentraliser := function(pr,ord,x,nr)
  # x an involution in G
  local i,l,y;
  l := [];
  for i in [1..nr] do   # find 20 generators of the centraliser
      y := RECOG.CentralisingElementOfInvolution(pr,ord,x);
      AddSet(l,y);
  od;
  return l;
end;


# See http://www.math.rwth-aachen.de/~Max.Neunhoeffer/Publications/pdf/perth09_handout.pdf
RECOG.InvolutionJumper := function(pr,ord,x,tol,withodd)
  # x an involution in a group g, for which the product replacer pr produces
  # random elements, withodd is true or false, it switches the odd case on or
  # off, ord an order oracle
  local c,count,o,y,z;
  count := 0;
  repeat
      count := count + 1;
      y := Next(pr);
      c := Comm(x,y);
      o := ord(c);
      if o = 1 then continue; fi;
      if IsEvenInt(o) then
          return c^(o/2);
      fi;
      if not(withodd) then continue; fi;
      z := y*c^((o-1)/2);
      o := ord(z);
      if IsEvenInt(o) then
          return z^(o/2);
      fi;
  until count > tol;
  return fail;
end;

RECOG.DirectFactorsFinder := function(gens,facgens,k,eq)
  local equal,fgens,i,j,l,o,pgens,pr,z;
  fgens := [];
  pr := ProductReplacer(facgens);
  Add(fgens,Next(pr));
  Add(fgens,Next(pr));
  if eq(fgens[1]*fgens[2],fgens[2]*fgens[1]) and
     eq(fgens[1]*fgens[3],fgens[3]*fgens[1]) then
      if eq(fgens[2]*fgens[3],fgens[3]*fgens[2]) then
          i := 0;
          while i <= 4 do
              Add(fgens,Next(pr),1);
              if ForAny([2..Length(fgens)],
                        j->not(eq(fgens[1]*fgens[j],fgens[j]*fgens[1]))) then
                  break;
              fi;
              i := i + 1;
          od;
          if i > 4 then
              Info(InfoRecog,2,"D247: did not find non-commuting elements.");
              return fail;
          fi;
      else
          fgens{[1..2]} := fgens{[2,1]};
      fi;
  fi;

  equal := function(a,b)
    return ForAny(b,y-> not(eq(a*y,y*a)));
  end;

  # Enumerate orbit:
  o := [fgens];
  pgens := List([1..Length(gens)],j->EmptyPlist(k));
  i := 1;
  while i <= Length(o) do
    for j in [1..Length(gens)] do
      z := o[i][1]^gens[j];
      l := 1;
      while l <= Length(o) and not(equal(z,o[l])) do
          l := l + 1;
      od;
      pgens[j][i] := l;
      if l > Length(o) then
        z := Concatenation([z],List(o[i]{[2..Length(o[i])]},x->x^gens[j]));
        Add(o,z);
        if Length(o) > k then
            Info(InfoRecog,1,
                 "Strange, found more direct factors than expected!");
            return fail;
        fi;
      fi;
    od;
    i := i + 1;
  od;

  if Length(o) < k then
      Info(InfoRecog,1,"Strange, found less direct factors than expected!");
      return fail;
  fi;

  pgens := List(pgens,PermList);
  if fail in pgens then return fail; fi;
  return [o,pgens];
end;

RECOG.DirectFactorsAction := function(data,el)
  local equal,i,j,res,z,o,eq;

  eq := data.eq;
  o := data.o;

  equal := function(a,b)
    return ForAny(b,y-> not(eq(a*y,y*a)));
  end;

  res := EmptyPlist(Length(o));
  for i in [1..Length(o)] do
    z := o[i][1]^el;
    j := 1;
    while j <= Length(o) and not(equal(z,o[j])) do
        j := j + 1;
    od;
    if j <= Length(o) then
      Add(res,j);
    else
      return fail;
    fi;
  od;
  return PermList(res);
end;

RECOG.IsPower := function(d)
  local f, e, g, l, dd;
  # Intended for small d
  f := Collected(Factors(d));
  e := List(f,x->x[2]);
  g := Gcd(e);
  d := DivisorsInt(g);
  d := d{[2..Length(d)]};
  l := EmptyPlist(Length(d));
  for dd in d do
    Add(l,[Product(f,x->x[1]^(x[2]/dd)),dd]);
  od;
  return l;
end;

RECOG.SortOutReducibleNormalSubgroup :=
  function(ri,G,ngens,m)
    # ngens generators for a proper normal subgroup, m a reducible
    # MeatAxe module with generators ngens.
    # This function takes care of the cases to construct a reduction.
    # Only call this with absolutely irreducible G!
    # Only call this if we already know that G is not C3!

    local H,a,basis,collf,conjgensG,f,hom,homcomp,homs,homsimg,kro,o,r,subdim;

    f := ri!.field;
    collf := MTX.CollectedFactors(m);
    if Length(collf) = 1 then    # only one homogeneous component!
        if MTX.Dimension(collf[1][1]) = 1 then
            # If we get here, the computed normal closure cannot be normal
            # since if m were semisimple, then all generators would be scalar
            # which they were not. So we conclude that FastNormalClosure
            # did not compute the full normal closure and for the moment
            # give up.
            # Usually this should have been caught by using projective orders.
            Info(InfoRecog,2,"D247:Scalar subgroup, FastNormalClosure must ",
                 "have made a mistake!");
            return TemporaryFailure;
        fi;
        Info(InfoRecog,2,"D247:Restriction to normal subgroup is homogeneous.");
        if not(MTX.IsAbsolutelyIrreducible(collf[1][1])) then
            Error("Is this really possible??? G acts absolutely irred!");
        fi;
        homs := MTX.Homomorphisms(collf[1][1],m);
        basis := Concatenation(homs);
# FIXME: This will go:
        ConvertToMatrixRep(basis,Size(f));
        subdim := MTX.Dimension(collf[1][1]);
        r := rec(t := basis, ti := basis^-1,
                 blocksize := MTX.Dimension(collf[1][1]));
        # Note that we already checked for semilinear, so we know that
        # the irreducible N-submodule is absolutely irreducible!
        # Now we believe to have a tensor decomposition:
        conjgensG := List(GeneratorsOfGroup(G),x->r.t * x * r.ti);
        kro := List(conjgensG,g->RECOG.IsKroneckerProduct(g,r.blocksize));
        if not(ForAll(kro,k->k[1] = true)) then
            Info(InfoRecog,1,"VERY, VERY, STRANGE!");
            Info(InfoRecog,1,"False alarm, was not a tensor decomposition.");
            Error("This should never have happened (346), tell Max.");
        fi;

        H := GroupWithGenerators(conjgensG);
        hom := GroupHomByFuncWithData(G,H,RECOG.HomDoBaseChange,r);
        SetHomom(ri,hom);

        # Hand down information:
        forfactor(ri).blocksize := r.blocksize;
        forfactor(ri).generatorskronecker := kro;
        Add( forfactor(ri).hints,
             rec( method := FindHomMethodsProjective.KroneckerProduct,
                  rank := 4000, stamp := "KroneckerProduct" ) );
        # This is an isomorphism:
        findgensNmeth(ri).method := FindKernelDoNothing;
        ri!.comment := "_D4TensorDec";
        return Success;
    fi;
    Info(InfoRecog,2,"D247:Using action on the set of homogeneous components",
           " (",Length(collf)," elements)...");
    # Now find a homogeneous component to act on it:
    homs := MTX.Homomorphisms(collf[1][1],m);
    if Length(homs) = 0 then
        Info(InfoRecog,2,"Restricted module not semisimple ==> not normal");
        return TemporaryFailure;
    fi;
    homsimg := BasisVectors(Basis(VectorSpace(f,Concatenation(homs))));
    homcomp := MutableCopyMat(homsimg);
# FIXME: This will go:
ConvertToMatrixRep(homcomp,Size(f));
    TriangulizeMat(homcomp);
    o := Orb(G,homcomp,OnSubspacesByCanonicalBasis,rec(storenumbers := true));
    Enumerate(o,QuoInt(ri!.dimension,Length(homcomp)));
    if not(IsClosed(o)) then
        Info(InfoRecog,2,"D247:Obviously did not get normal subgroup!");
        return TemporaryFailure;
    fi;

    # NOTE: here we switch from matrix to permutation group recognition!
    # Here is an example triggering this:
    #
    # gap> n:=7;; G:=AlternatingGroup(n);;
    # gap> gens:=List(GeneratorsOfGroup(G),g->PermutationMat(g,n)) * Z(5);;
    # gap> gens[1][1][2] := -gens[1][1][2];; gens[2][7][5] := -gens[2][7][5];;
    # gap> H2:=Group(gens);; ri:=RecognizeGroup( H2 );
    # gap> Grp(RIFac(ri));
    # <matrix group with 2 generators>
    # gap> Grp(RIFac(RIFac(ri)));
    # Group([ (1,2,3,4,5,6,7), (1,2,3) ])

    a := OrbActionHomomorphism(G,o);
    SetHomom(ri,a);
    Setmethodsforfactor(ri,FindHomDbPerm);
    ri!.comment := "_D2Imprimitive";
    Setimmediateverification(ri,true);
    findgensNmeth(ri).args[1] := Length(o)+6;
    findgensNmeth(ri).args[2] := 4;
    return Success;
  end;

RECOG.SortOutReducibleSecondNormalSubgroup :=
  function(ri,G,nngens,mm)
    # nngens generators for a proper normal subgroup of a proper
    # irreducible normal subgroup, mm a reducible MeatAxe module with
    # generators nngens.
    # This function takes care of the cases to construct a reduction
    # if we have a D7 case.
    # Only call this with absolutely irreducible G!
    # Only call this if we already know that G is not C3!
    # Only call this if the upper normal subgroup was still irreducible!

    local H,collf,dim,hom,mult,orb,subdim;

    collf := MTX.CollectedFactors(mm);
    if Length(collf) = 1 then
        subdim := MTX.Dimension(collf[1][1]);
        dim := MTX.Dimension(mm);
        mult := First([2..20],i->subdim^i = dim);
        if mult <> fail then
            orb := RECOG.DirectFactorsFinder(GeneratorsOfGroup(G),
                                             nngens,mult,ri!.isequal);
            if orb <> fail then
                H := GroupWithGenerators(orb[2]);
                hom := GroupHomByFuncWithData(G,H,
                           RECOG.DirectFactorsAction,
                           rec( o := orb[1], eq := ri!.isequal) );
                SetHomom(ri,hom);
                Setmethodsforfactor(ri,FindHomDbPerm);
                Info(InfoRecog,2,"D247: Success, found D7 with action",
                     " on ",mult," direct factors.");
                ri!.comment := "_D7TensorInduced";
                return Success;
            else
                Info(InfoRecog,2,"D247: Did not find direct factors!");
            fi;
        else
            Info(InfoRecog,2,"D247: Submodule dimension no root!");
        fi;
    else
        Info(InfoRecog,2,"D247: Restriction not homogeneous!");
    fi;
    return fail; # FIXME: fail = TemporaryFailure here really correct?
  end;

FindHomMethodsProjective.D247 := function(ri,G)
  # We try to produce an element of a normal subgroup by playing
  # tricks.
  local CheckNormalClosure,f,i,res,x,ispower;

  RECOG.SetPseudoRandomStamp(G,"D247");

  CheckNormalClosure := function(x)
    # This is called with an element that we hope lies in a normal subgroup.
    local H,a,basis,collf,conjgensG,count,dim,hom,homcomp,homs,homsimg,i,
          kro,m,mm,mult,ngens,nngens,o,orb,pr,r,subdim,y,z;
    ngens := FastNormalClosure(GeneratorsOfGroup(G),[x],4);
    m := GModuleByMats(ngens,f);
    if MTX.IsIrreducible(m) then
        if not(ispower) then
            Info(InfoRecog,4,"Dimension is no power!");
            return fail; # FIXME: fail = TemporaryFailure here really correct?
        fi;
        # we want to look for D7 here, using the same trick again:
        count := 0;
        #n := GroupWithGenerators(ngens);
        pr := ProductReplacer(ngens);
        y := RECOG.InvolutionJumper(pr,RECOG.ProjectiveOrder,x,200,false);
        if y = fail then
            return TemporaryFailure;
        fi;
        for i in [1..3] do
            z := RECOG.InvolutionJumper(pr,RECOG.ProjectiveOrder,y,200,false);
            if z <> fail then y := z; fi;
        od;
        nngens := FastNormalClosure(ngens,[y],2);
        mm := GModuleByMats(nngens,f);
        if not(MTX.IsIrreducible(mm)) then
            return RECOG.SortOutReducibleSecondNormalSubgroup(ri,G,nngens,mm);
        fi;
        return fail; # FIXME: fail = TemporaryFailure here really correct?
    fi;
    if InfoLevel(InfoRecog) >= 2 then Print("\n"); fi;
    Info(InfoRecog,2,"D247: Seem to have found something!");
    return RECOG.SortOutReducibleNormalSubgroup(ri,G,ngens,m);
  end;

  Info(InfoRecog,2,"D247: Trying the involution jumper 9 times..."); # FIXME: don't hardcode '9'
  f := ri!.field;
  ispower := Length(RECOG.IsPower(ri!.dimension)) > 0;
  x := RECOG.InvolutionSearcher(ri!.pr,RECOG.ProjectiveOrder,100);
  if x = fail then
      Info(InfoRecog,2,"Did not find an involution! Giving up.");
      return TemporaryFailure;
  fi;

  for i in [1..9] do
      if InfoLevel(InfoRecog) >= 2 then Print(".\c"); fi;
      res := CheckNormalClosure(x);
      if res in [true,false] then return res; fi;
      x := RECOG.InvolutionJumper(ri!.pr,RECOG.ProjectiveOrder,x,100,true);
      if x = fail then
          if InfoLevel(InfoRecog) >= 2 then Print("\n"); fi;
          Info(InfoRecog,2,"Involution Jumper failed, giving up!");
          return TemporaryFailure;
      fi;
  od;
  res := CheckNormalClosure(x);
  if res in [true,false] then return res; fi;
  if InfoLevel(InfoRecog) >= 2 then Print("\n"); fi;
  Info(InfoRecog,2,"D247: Did not find normal subgroup, giving up.");
  return TemporaryFailure;
end;

# FIXME: PrototypeForC2C4 is not used anywhere
FindHomMethodsProjective.PrototypeForC2C4 := function(ri,G)
  # We try to produce an element of a normal subgroup by playing
  # tricks.
  local CheckNormalClosure,f,m,res,ngens,l;

  RECOG.SetPseudoRandomStamp(G,"PrototypeForC2C4");
  f := ri!.field;

  CheckNormalClosure := function(x)
    # This is called with an element that we hope lies in a normal subgroup.
    local m,ngens;
    ngens := FastNormalClosure(GeneratorsOfGroup(G),x,4);
    m := GModuleByMats(ngens,f);
    if not(IsIrreducible(m)) then
        Info(InfoRecog,2,"Proto: Seem to have found something!");
        return RECOG.SortOutReducibleNormalSubgroup(ri,G,ngens,m);
    else
        return fail;
    fi;
  end;

  Info(InfoRecog,2,"Proto: Starting to work...");

  # Make some elements l which have good chances to be in a normal subgroup
  # ...
  # Then do:
  res := CheckNormalClosure(l);
  if res = true then
      Info(InfoRecog,2,"Proto: Found a reduction.");
      return true;
  fi;

  Info(InfoRecog,2,"Proto: Did not find normal subgroup, giving up.");
  return fail;
end;

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

