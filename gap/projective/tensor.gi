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
      N := GroupWithGenerators(FastNormalClosure(G,[c],10));
      if onlyone and
         (ForAny(GeneratorsOfGroup(N),m->IsZero(m[1,1]) or
                                         not IsOne(m*(m[1,1])^-1))) then
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

  # Compute the homogeneous component:
  w := Last(m);   # An irreducible FN-module
  homs := MTX.Homomorphisms(w,m[1]);
  homsimg := Concatenation(homs);
  ConvertToMatrixRep(homsimg,f);
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
      ErrorNoReturn("This should never have happened (1), talk to Max.");
  fi;
  # homsimg is a basis of an N-homogeneous component.
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
          if not c in lset then
              Add(h,h[i]*g);
              Add(l,c);
              AddSet(lset,c);
          fi;
      od;
      i := i + 1;
  od;
  h := Concatenation(h);
  ConvertToMatrixRep(h,f);

  if i > Length(l) then    # by Clifford this should never happen, but still...
      if Length(l) = 1 then
          return fail;
      else
          # We have a (relatively short) non-trivial orbit!
          return rec(orbit := lset);
      fi;
  else
      ConvertToMatrixRep(basis,f);
      basisi := basis^-1;
      return rec(t := basis, ti := basisi, spaces := lset, field := f,
                 blocksize := Length(lset[1]));
  fi;
end;

RECOG.IsKroneckerProduct := function(m,r)
  local blocksize,a,ac,ar,b,blockpos,d,entrypos,i,j,mul,pos;
  blocksize := r.blocksize;
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
  ConvertToMatrixRep(a,r.field);
  ConvertToMatrixRep(ac,r.field);
  return [true,a,ac];
end;

# RECOG.VerifyTensorDecomposition := function(gens,r)
#   local g,newgens,newgensdec,res,yes;
#   newgens := List(gens,x->r.t * x * r.ti);
#   newgensdec := [];
#   yes := true;
#   for g in newgens do
#       res := RECOG.IsKroneckerProduct(g,r);
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
#
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
#       if x <> fail and not RECOG.IsScalarMat(x) then
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


#! @BeginChunk TensorDecomposable
#! This method looks for the tensor-decomposable situation described in
#! <Cite Key="Neu09" Where="Section VII.(6.6)"/>. It first searches for a
#! non-scalar normal subgroup
#! whose restriction to the natural module is homogeneous. From such a
#! subgroup it reconstructs a basis in which the group acts by Kronecker
#! products. If the homogeneous constituent is not absolutely irreducible,
#! then the same setup instead points to a semilinear structure; otherwise it
#! yields a genuine tensor decomposition.
#! 
#! In practical terms the implementation starts from random elements and their
#! commutators to obtain suitable normal subgroups, then uses MeatAxe data for
#! the restriction to that subgroup to build the actual tensor basis, as in
#! Lemma VII.6.6 and Theorem VII.6.7 of <Cite Key="Neu09"/>.
#! @EndChunk
BindRecogMethod("FindHomMethodsProjective", "TensorDecomposable",
"find a tensor decomposition",
function(ri)
  local G,H,N,conjgensG,d,f,hom,kro,r;

  G := Grp(ri);
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
      Setmethodsforimage(ri,FindHomDbPerm);
      return Success;
  fi;

  Info(InfoRecog,2,
       "TensorDecomposable: I seem to have found a tensor decomposition.");

  # Now we believe to have a tensor decomposition:
  conjgensG := List(GeneratorsOfGroup(G),x->r.t * x * r.ti);
  kro := List(conjgensG,g->RECOG.IsKroneckerProduct(g,r));
  if not ForAll(kro, k -> k[1]) then
      Info(InfoRecog,1,"VERY, VERY, STRANGE!");
      Info(InfoRecog,1,"False alarm, was not a tensor decomposition.",
           " Found at least a perm action.");
      hom := ActionHomomorphism(G,r.spaces,OnSubspacesByCanonicalBasis,
                                "surjective");
      SetHomom(ri,hom);
      Setmethodsforimage(ri,FindHomDbPerm);
      return Success;
  fi;

  H := GroupWithGenerators(conjgensG);
  hom := GroupHomByFuncWithData(G,H,RECOG.HomDoBaseChange,r);
  SetHomom(ri,hom);

  # Hand down information:
  InitialDataForImageRecogNode(ri).blocksize := r.blocksize;
  InitialDataForImageRecogNode(ri).generatorskronecker := kro;
  AddMethod(InitialDataForImageRecogNode(ri).hints, FindHomMethodsProjective.KroneckerProduct, 2000);
  # This is an isomorphism:
  findgensNmeth(ri).method := FindKernelDoNothing;
  return Success;
end);

RECOG.HomTensorFactor := function(data,m)
  local k;
  k := RECOG.IsKroneckerProduct(m,data);
  if k[1] <> true then
      return fail;
  fi;
  return k[3];
end;

#! @BeginChunk KroneckerProduct
#! This method is only used after a previous step has already found a tensor
#! decomposition and rewritten the generators accordingly. It projects to one
#! tensor factor, recognises that factor projectively, and then continues with
#! the other factor in the kernel.
#!
#! The underlying tensor-decomposition argument is the one used for the
#! tensor-decomposable case in <Cite Key="Neu09"
#! Where="Section VII.(6.6), especially pp. 125-126"/>: after a suitable base
#! change, and using the constructive reduction from Theorem VII.6.7, each
#! group element acts as a Kronecker product on
#! <M>V_1 \otimes_{\mathbb{F}_q} V_2</M>. In projective recognition one has to allow
#! for scalar ambiguity in the extracted tensor factor, so the generic
#! projective SLP machinery must treat representatives up to scalars.
#! @EndChunk
BindRecogMethod("FindHomMethodsProjective", "KroneckerProduct",
"split off one factor of a tensor decomposition projectively",
function(ri)
  # We got the hint that this is a Kronecker product, let's take it apart.
  # We first recognise projectively in one tensor factor and then in the
  # other, life is easy because of projectiveness!
  local G,H,data,hom,newgens;
  G := Grp(ri);
  newgens := List(ri!.generatorskronecker,x->x[3]);
  H := GroupWithGenerators(newgens);
  data := rec(blocksize := ri!.blocksize, field := ri!.field);
  hom := GroupHomByFuncWithData(G,H,RECOG.HomTensorFactor,data);
  SetHomom(ri,hom);

  AddMethod(InitialDataForKernelRecogNode(ri).hints, FindHomMethodsProjective.KroneckerKernel, 2000);
  InitialDataForKernelRecogNode(ri).blocksize := ri!.blocksize;
  return Success;
end);

RECOG.HomTensorKernel := function(data,m)
  local mm;
  mm := ExtractSubMatrix(m,[1..data.blocksize],[1..data.blocksize]);
  MakeImmutable(mm);
  return mm;
end;

#! @BeginChunk KroneckerKernel
#! This method handles the kernel left behind by
#! <Ref Subsect="KroneckerProduct" Style="Text"/>. In that kernel the second
#! tensor factor is projectively scalar, so every element is represented by a
#! block-diagonal matrix with identical diagonal blocks. The homomorphism used
#! here simply projects to one of those blocks.
#!
#! As for <Ref Subsect="KroneckerProduct" Style="Text"/>, this is part of the
#! tensor-decomposition strategy discussed in <Cite Key="Neu09"
#! Where="Section VII.(6.6), especially p. 126"/>.
#! @EndChunk
BindRecogMethod("FindHomMethodsProjective", "KroneckerKernel",
"project from the tensor kernel to the repeated diagonal block",
function(ri)
  # One up in the tree we got the hint about a Kronecker product, this
  # method is called when we have gone to one factor and now are in the
  # kernel. So we know that we are a block diagonal matrix with identical
  # diagonal blocks. All we do is to project down to one of the blocks.
  local G,H,data,hom,newgens;
  G := Grp(ri);
  data := rec(blocksize := ri!.blocksize, field := ri!.field);
  newgens := List(GeneratorsOfGroup(G),x->RECOG.HomTensorKernel(data,x));
  H := GroupWithGenerators(newgens);
  hom := GroupHomByFuncWithData(G,H,RECOG.HomTensorKernel,data);
  SetHomom(ri,hom);
  findgensNmeth(ri).method := FindKernelDoNothing;
  return Success;
end);
