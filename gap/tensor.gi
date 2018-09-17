#############################################################################
##
##  tensor.gi
##                                recog package
##                                                        Max Neunhoeffer
##                                                            Ákos Seress
##
##  Copyright 2005-2008 by the authors.
##  This file is free software, see license information at the end.
##
##  A collection of find homomorphism methods for tensor product
##  decompositions of matrix groups.
##
#############################################################################

RECOG.FindTensorKernel := function(G,onlyone)
  # Assume G respects a tensor product decomposition of its natural
  # module V. Try to find the kernel of the canonical map:
  local N,allps,c,fac,facs,i,j,kgens,newc,notused,o,pfacs,x,z;
  kgens := [];
  for i in [1..5] do
      x := PseudoRandom(G);
      o := ProjectiveOrder(x)[1];
      fac := Collected(Factors(Integers,o));
      pfacs := List(fac,x->x[1]);
      allps := Product(pfacs);
      z := x^(o/allps);
      #Print(pfacs,"\n");
      for j in pfacs do
          #Print(j," \c");
          Add(kgens,z^(allps/j));
              # make a prime element, hope it is in the kernel
      od;
      #Print("\n");
  od;

  # Now we hope that at least one of the elements in kgens is in the kernel,
  # we do something to ensure that in that case we have a kernel element:
  facs := [];
  while Length(kgens) > 0 do
      #Print(Length(kgens)," \c");
      c := kgens[1];
      notused := [];
      for i in [2..Length(kgens)] do
          newc := Comm(c,kgens[i]);
          if IsOneProjective(newc) then
              x := PseudoRandom(G);
              newc := Comm(c,kgens[i]^x);
              if IsOneProjective(newc) then
                  Add(notused,kgens[i]);
              else
                  c := newc;
              fi;
          else
              c := newc;
          fi;
      od;
      #Print(Length(notused)," \c");
      N := GroupWithGenerators(FastNormalClosure(GeneratorsOfGroup(G),[c],10));
      if onlyone and
         (ForAny(GeneratorsOfGroup(N),m->IsZero(m[1,1]) or
                                         not(IsOne(m*(m[1,1])^-1)))) then
          # we found a non-scalar normal subgroup:
          #Print("\n");
          return N;
      fi;
      Add(facs,N);
      kgens := notused;
  od;
  #Print("\n");
  return facs;
end;

RECOG.FindTensorDecomposition := function(G,N)
  # N a non-scalar normal subgroup of G
  local b,basis,basisi,c,d,f,g,gens,gensn,h,homs,homsimg,i,l,lset,m,n,subdim,w;

  d := DimensionOfMatrixGroup(G);

  # First find an irreducible N-submodule of the natural module:
  f := FieldOfMatrixGroup(G);
  gensn := GeneratorsOfGroup(N);
  # FIXME: necessary:?
  #if IsObjWithMemory(gensn[1]) then
  #    gensn := StripMemory(gensn);
  #fi;
  m := [GModuleByMats(gensn,f)];
  n := [MTX.ProperSubmoduleBasis(m[1])];
  if n[1] = fail then
      # This means the restriction is irreducible, we cannot do anything here
      return fail;
  fi;
  i := 1;
  while n[i] <> fail do
      Add(m,MTX.InducedActionSubmodule(m[i],n[i]));
      Add(n,MTX.ProperSubmoduleBasis(m[i+1]));
      i := i + 1;
  od;
  i := i - 1;
  b := n[i];
  i := i - 1;
  while i >= 1 do
      b := b * n[i];
      i := i - 1;
  od;

  # Compute the homogeneous component:
  w := m[Length(m)];   # An irreducible FN-module
  homs := MTX.Homomorphisms(w,m[1]);
  homsimg := Concatenation(homs);
  # FIXME:
  ConvertToMatrixRep(homsimg);
  if Length(homsimg) = d then    # we see one homogeneous component
      basis := homsimg;
      basisi := homsimg^-1;
      # In this case we will have a tensor decomposition:
      subdim := MTX.Dimension(w);
      if MTX.IsAbsolutelyIrreducible(w) then
          # This is a genuine tensor decomposition:
          return rec(t := basis, ti := basisi, blocksize := subdim);
      fi;
      # Otherwise we have a tensor decomposition over a bigger field:
      # This will not be reached, since we have made sure that
      # semilinear already caught this. (Lemma: If one tensor factor is
      # semilinear, then the product is.)
      Error("This should never have happened (1), talk to Max.");
  fi;
  # homsimg is a basis of an N-homogenous component.
  # We move that one around with G to find a basis of the natural module:
  # By Clifford's theorem this is a block system:
  if d mod Length(homsimg) <> 0 then
      # Not a homogeneous component, obviously we did not find
      # a normal subgroup for some reason!
      return fail;
  fi;

  h := [ShallowCopy(homsimg)];
  b := MutableCopyMat(homsimg);
  TriangulizeMat(b);
  l := [b];
  lset := [b];
  gens := GeneratorsOfGroup(G);
  i := 1;
  while Length(h) < d/Length(homsimg) and i <= Length(l) do
      for g in gens do
          c := OnSubspacesByCanonicalBasis(l[i],g);
          if not(c in lset) then
              Add(h,h[i]*g);
              Add(l,c);
              AddSet(lset,c);
          fi;
      od;
      i := i + 1;
  od;
  h := Concatenation(h);
  ConvertToMatrixRep(h);

  if i > Length(l) then    # by Clifford this should never happen, but still...
      if Length(l) = 1 then
          return fail;
      else
          # We have a (relatively short) non-trivial orbit!
          return rec(orbit := lset);
      fi;
  else
      ConvertToMatrixRep(basis);
      basisi := basis^-1;
      return rec(t := basis, ti := basisi, spaces := lset,
                 blocksize := Length(lset[1]));
  fi;
end;

RECOG.IsKroneckerProduct := function(m,blocksize)
  local a,ac,ar,b,blockpos,d,entrypos,i,j,mul,pos;
  if Length(m) mod blocksize <> 0 then
      return [false];
  fi;
  d := Length(m);
  pos := PositionNonZero(m[1]);
  blockpos := QuoInt(pos-1,blocksize)+1;
  entrypos := ((pos-1) mod blocksize)+1;
  a := ExtractSubMatrix(m,[1..blocksize],
                          [(blockpos-1)*blocksize+1..blockpos*blocksize]);
  a := a/a[1,entrypos];
  ac := [];
  for i in [1..d/blocksize] do
      ar := [];
      for j in [1..d/blocksize] do
          b := ExtractSubMatrix(m,[(i-1)*blocksize+1..i*blocksize],
                                  [(j-1)*blocksize+1..j*blocksize]);
          mul := b[1,entrypos];
          if a * mul <> b then
              return [false];
          fi;
          Add(ar,mul);
      od;
      Add(ac,ar);
  od;
  # FIXME:
  ConvertToMatrixRep(a);
  ConvertToMatrixRep(ac);
  return [true,a,ac];
end;

# RECOG.VerifyTensorDecomposition := function(gens,r)
#   local g,newgens,newgensdec,res,yes;
#   newgens := List(gens,x->r.t * x * r.ti);
#   newgensdec := [];
#   yes := true;
#   for g in newgens do
#       res := RECOG.IsKroneckerProduct(g,r.blocksize);
#       if res[1] = false then
#           Add(newgensdec,fail);
#           yes := false;
#       else
#           Add(newgensdec,[res[2],res[3]]);
#       fi;
#   od;
#   return [yes,newgens,newgensdec];
# end;
#
# RECOG.FindInvolution := function(g)
#   # g a matrix group
#   local i,o,x;
#   for i in [1..100] do
#       x := PseudoRandom(g);
#       o := Order(x);
#       if o mod 2 = 0 then
#           return x^(o/2);
#       fi;
#   od;
#   return fail;
# end;
# 
# RECOG.FindCentralisingElementOfInvolution := function(G,x)
#   # x an involution in G
#   local o,r,y,z;
#   r := PseudoRandom(G);
#   y := x^r;
#   # Now x and y generate a dihedral group
#   if x=y then return r; fi;
#   z := x*y;
#   o := Order(z);
#   if IsEvenInt(o) then
#       return z^(o/2);
#   else
#       return z^((o+1)/2)*r^(-1);
#   fi;
# end;

RECOG.IsScalarMat := function(m)
  local i,x;
  if not(IsDiagonalMat(m)) then
      return false;
  fi;
  x := m[1,1];
  for i in [2..Length(m)] do
      if m[i,i] <> x then
          return false;
      fi;
  od;
  return x;
end;

# RECOG.FindInvolutionCentraliser := function(G,x)
#   # x an involution in G
#   local i,l,y;
#   l := [];
#   for i in [1..20] do   # find 20 generators of the centraliser
#       y := RECOG.FindCentralisingElementOfInvolution(G,x);
#       AddSet(l,y);
#   od;
#   return GroupWithGenerators(l);
# end;
#
#
# RECOG.FindTensorOtherFactor := function(G,N,blocksize)
#   # N a non-scalar normal subgroup of G
#   # Basechange already done such that N is a block scalar matrix meaning
#   # "block-diagonal" and all blocks along the diagonal are equal.
#   local c,i,invs,o,out,timeout,x,z;
# 
#   # Find a non-scalar involution in N:
#   timeout := 100;
#   while true do
#       timeout := timeout - 1;
#       if timeout = 0 then return fail; fi;
#       x := RECOG.FindInvolution(N);
#       if x <> fail and RECOG.IsScalarMat(x) = false then
#           break;
#       fi;
#   od;
# 
#   invs := [x];
#   for i in [1..5] do
#       Add(invs,x^PseudoRandom(N));
#   od;
# 
#   timeout := 100;
#   while true do
#       timeout := timeout - 1;
#       if timeout = 0 then return fail; fi;
#       c := RECOG.FindCentralisingElementOfInvolution(G,invs[1]);
#       o := Order(c);
#       if IsOddInt(o) then continue; fi;
#       c := c^(o/2);
#       i := 2;
#       out := false;
#       while i <= 5 do
#           x := invs[i] * c;
#           o := Order(x);
#           if IsOddInt(o) then break; fi;
#           z := x^(o/2);   # this now commutes with invs[1]..invs[i], because
#                           # it is a power of a product of inv
#       od;
#   od;
# end;


FindHomMethodsProjective.TensorDecomposable := function(ri,G)
  local H,N,conjgensG,d,f,hom,kro,r;

  RECOG.SetPseudoRandomStamp(G,"TensorDecomposable");

  # Here we probably want to do an order test and even a polynomial
  # factorization test... Later!
  # Do we want?

  d := ri!.dimension;
  if IsPrime(d) then
      return NeverApplicable;
  fi;
  f := ri!.field;

  # Now assume a tensor factorization exists:
  #Gm := GroupWithMemory(G);???
  N := RECOG.FindTensorKernel(G,true);
  Info(InfoRecog,3,
       "TensorDecomposable: I seem to have found a normal subgroup...");
  r := RECOG.FindTensorDecomposition(G,N);
  if r = fail then
      return TemporaryFailure;
  fi;
  if IsBound(r.orbit) then
      Info(InfoRecog,2,"Did not find tensor decomposition but orbit.");
      # We did not find a tensor decomposition, but a relatively short orbit:
      hom := ActionHomomorphism(G,r.orbit,OnSubspacesByCanonicalBasis,
                                "surjective");
      SetHomom(ri,hom);
      Setmethodsforfactor(ri,FindHomDbPerm);
      return Success;
  fi;

  Info(InfoRecog,2,
       "TensorDecomposable: I seem to have found a tensor decomposition.");

  # Now we believe to have a tensor decomposition:
  conjgensG := List(GeneratorsOfGroup(G),x->r.t * x * r.ti);
  kro := List(conjgensG,g->RECOG.IsKroneckerProduct(g,r.blocksize));
  if not(ForAll(kro,k->k[1] = true)) then
      Info(InfoRecog,1,"VERY, VERY, STRANGE!");
      Info(InfoRecog,1,"False alarm, was not a tensor decomposition.",
           " Found at least a perm action.");
      hom := ActionHomomorphism(G,r.spaces,OnSubspacesByCanonicalBasis,
                                "surjective");
      SetHomom(ri,hom);
      Setmethodsforfactor(ri,FindHomDbPerm);
      return Success;
  fi;

  H := GroupWithGenerators(conjgensG);
  hom := GroupHomByFuncWithData(G,H,RECOG.HomDoBaseChange,r);
  SetHomom(ri,hom);

  # Hand down information:
  forfactor(ri).blocksize := r.blocksize;
  forfactor(ri).generatorskronecker := kro;
  Add( forfactor(ri).hints,
       rec( method := FindHomMethodsProjective.KroneckerProduct, rank := 2000,
            stamp := "KroneckerProduct" ), 1 );
  # This is an isomorphism:
  findgensNmeth(ri).method := FindKernelDoNothing;
  return Success;
end;

RECOG.HomTensorFactor := function(data,m)
  local k;
  k := RECOG.IsKroneckerProduct(m,data.blocksize);
  if k[1] <> true then return fail; fi;
  return k[3];
end;

FindHomMethodsProjective.KroneckerProduct := function(ri,G)
  # We got the hint that this is a Kronecker product, let's take it apart.
  # We first recognise projectively in one tensor factor and then in the
  # other, life is easy because of projectiveness!
  local H,data,hom,newgens;
  newgens := List(ri!.generatorskronecker,x->x[3]);
  H := GroupWithGenerators(newgens);
  data := rec(blocksize := ri!.blocksize);
  hom := GroupHomByFuncWithData(G,H,RECOG.HomTensorFactor,data);
  SetHomom(ri,hom);

  Add( forkernel(ri).hints,
       rec( method := FindHomMethodsProjective.KroneckerKernel, rank := 2000,
            stamp := "KroneckerKernel" ), 1);
  forkernel(ri).blocksize := ri!.blocksize;
  return Success;
end;

RECOG.HomTensorKernel := function(data,m)
  local mm;
  mm := ExtractSubMatrix(m,[1..data.blocksize],[1..data.blocksize]);
  MakeImmutable(mm);
  return mm;
end;

FindHomMethodsProjective.KroneckerKernel := function(ri,G)
  # One up in the tree we got the hint about a Kronecker product, this
  # method is called when we have gone to one factor and now are in the
  # kernel. So we know that we are a block diagonal matrix with identical
  # diagonal blocks. All we do is to project down to one of the blocks.
  local H,data,hom,newgens;
  data := rec(blocksize := ri!.blocksize);
  newgens := List(GeneratorsOfGroup(G),x->RECOG.HomTensorKernel(data,x));
  H := GroupWithGenerators(newgens);
  hom := GroupHomByFuncWithData(G,H,RECOG.HomTensorKernel,data);
  SetHomom(ri,hom);
  findgensNmeth(ri).method := FindKernelDoNothing;
  return Success;
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

