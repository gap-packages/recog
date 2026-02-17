#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This files's authors include Max Neunhöffer, Ákos Seress, Daniel Rademacher.
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


#! @BeginChunk TensorDecomposable
#! TODO/FIXME: it is unclear if the following description actually belongs
#! to this method, so be cautious!
#! 
#! 
#! This method currently tries to find one tensor factor by powering up
#! commutators of random elements to elements of prime order. This seems
#! to work quite well provided that the two tensor factors are not
#! <Q>linked</Q> too much such that there exist enough elements that act
#! with different orders on both tensor factors.
#! 
#! This method and its description needs some improvement.
#! @EndChunk
BindRecogMethod(FindHomMethodsProjective, "TensorDecomposable",
"find a tensor decomposition",
function(ri,G)
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
      Setmethodsforimage(ri,FindHomDbPerm);
      return Success;
  fi;

  Info(InfoRecog,2,
       "TensorDecomposable: I seem to have found a tensor decomposition.");

  # Now we believe to have a tensor decomposition:
  conjgensG := List(GeneratorsOfGroup(G),x->r.t * x * r.ti);
  kro := List(conjgensG,g->RECOG.IsKroneckerProduct(g,r.blocksize));
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
  k := RECOG.IsKroneckerProduct(m,data.blocksize);
  if k[1] <> true then
      return fail;
  fi;
  return k[3];
end;

#! @BeginChunk KroneckerProduct
#! TODO
#! @EndChunk
BindRecogMethod(FindHomMethodsProjective, "KroneckerProduct",
"TODO",
function(ri, G)
  # We got the hint that this is a Kronecker product, let's take it apart.
  # We first recognise projectively in one tensor factor and then in the
  # other, life is easy because of projectiveness!
  local H,data,hom,newgens;
  newgens := List(ri!.generatorskronecker,x->x[3]);
  H := GroupWithGenerators(newgens);
  data := rec(blocksize := ri!.blocksize);
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
#! TODO
#! @EndChunk
BindRecogMethod(FindHomMethodsProjective, "KroneckerKernel",
"TODO",
function(ri, G)
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
end);


###################################################################################################
###################################################################################################
######## Tensor Products infrastructure ###########################################################
###################################################################################################
###################################################################################################


# Implemented by DR to keep track of the tensor stuff below.
RECOG.PrepareTensor := function(G)
local gens;

    gens := GeneratorsOfGroup(G);

    return rec( group := G, d := NumberRows(gens[1]), gens := gens, fld := FieldOfMatrixList(gens), IsTensorProduct := "unknown", TensorDimensions := "unknown",
              TensorBasis := "unknown", TensorProductFlag := "unknown", TensorFactors := "unknown");

end;



# {Return true if we know G is a tensor product,
# false if we know that G is not, otherwise "unknown"}
# G::GrpMat : Factors := [], Fast := false, RandomElements := 20
RECOG.IsTensor := function (G, Factors, Fast, RandomElements)
local a, flag, TM;
    
    if RecogniseClassical(G) <> "fail" then
        # TODO: We want
        # ClassicalType (G) eq "orthogonalplus"
        # But is there a naming algorithm for gray box groups in GAP so far?
        # And if yes, can the algorithm decide between the types?
        if (Degree (G) = 4) and (RecogniseClassical(G).IsSOContained = true) then 
            RandomElements := Maximum (RandomElements, 200);
        else
            return false;
        fi;
    fi;

    TM := RECOG.IsTensorMain(RECOG.PrepareTensor(G), false, Factors, Fast, RandomElements);
    if TM <> fail then
        return TM;
    else
        return "unknown";
    fi;
end;



RECOG.TensorDimension := function (G)
local fac, u, w;

    fac := G.TensorFactors;
    # Compute represent of factor 1 and factor 2
    u := NumberRows(GeneratorsOfGroup(fac[1]));
    w := NumberRows(GeneratorsOfGroup(fac[2]));
    G.TensorDimensions := [u, w];
    return [u, w];

end;


#{Return the change of basis matrix which exhibits the
# tensor decomposition of G};
RECOG.TensorBasis := function (G)

    if G.TensorBasis <> fail then
        return G.TensorBasis;
    fi;

    return "unknown";

end;


RECOG.SetTensorBasis := function (G, B)

    G.TensorBasis := B;

end;


RECOG.TensorProductFlag := function (G)

    if G.TensorProductFlag <> fail then
        return G.TensorProductFlag;
    fi;

    return "unknown";

end;


RECOG.SetTensorProductFlag := function (G, value)

    G.IsTensorProduct := value;

end;


RECOG.TensorFactors := function (G)

    if G.TensorFactors <> fail then
        return G.TensorFactors;
    fi;

    return "unknown";

end;


RECOG.SetTensorFactors := function (G, factors)

    G.TensorFactors := factors;

end;


RECOG.Normalise := function(M, F, zero, d)
local scaler, mat, row, col, notfound, scalerInv;

    scaler := zero;
    mat := IdentityMat(d,F);
    notfound := true;
    for row in [1..d] do
        if M[row,1] <> zero then
            if notfound then
                scaler := M[row,1];
                scalerInv := scaler^(-1);
                notfound := false;
            else
                mat[row,1] := M[row,1]*scalerInv;
            fi;
        else
            mat[row,1] := zero;
        fi;
    od;

    for row in [1..d] do
        for col in [2..d] do
            if M[row,col] <> zero then
                mat[row,col] := M[row,col]*scalerInv;
            else
                mat[row,col] := zero;
            fi;
        od;
    od;

    return [mat,scaler];
end;


#{ Decide whether or not the collection of matrices X is composed
#  of blocks size blockSize which differ only by scalars;
#  if so, return true and the decomposition of each matrix, else false.
#}
RECOG.DecomposeKronecker := function(X, blockSize)
local F, d, flag, nBlocks, components, decompositions, scalars, row, col, top, left, scalar, g, block, normalised;

    if Size(X) = 0 then
	    Print("Argument 1 must be non-empty\n");
        return [false,false];
    fi;
    
    F := FieldOfMatrixList(X);
    d := NrRows(X[1]);
    flag := IsInt(d/blockSize);
    if flag then   
        nBlocks := Int(d/blockSize);
    else
        return [false,false];
    fi;
    
    decompositions := [];
    
    for g in X do
        components := [];
        scalars := [];
        
        for row in [1 .. nBlocks] do
            for col in [1 .. nBlocks] do
                top  := (row - 1) * blockSize + 1;
                left := (col - 1) * blockSize + 1;
                
                block := g{[top..(top+blockSize-1)]}{[left..(left+blockSize-1)]};
                # Write function IsZero, i.e. at least one entry not zero;
                if IsZero(block) then
                    Add(scalars, Zero(F));
                else
                    normalised := RECOG.Normalise(block, F, Zero(F), blockSize);
                    scalar := normalised[2];
                    normalised := normalised[1];
                    
                    if Size(components) = 0 then
                        Add(components, normalised);
                    else
                        if normalised <> components[1] then
                            return [false, false];
                        fi;
                    fi;
                    
                    Add(scalars, scalar);
                fi;
            od;
        od;

        # All blocks zero?
        if Size(components) = 0 then
            return [false, false];
        fi;

        scalars := Matrix(IsPlistMatrixRep,F,scalars,blockSize);
        scalars := Unpack(scalars);

        Add(components, scalars);
        if KroneckerProduct(components[2], components[1]) <> g then
            Error("KroneckerDecomposition: What the hell did you do?");
        fi;

        Append(decompositions, Reversed(components));
    od;

    return [true, decompositions];
end;



#{Decide whether or not the collection of matrices X is composed of 
# k x k blocks which differ only by scalars; if so, return true and 
# the decomposition of each matrix, else false}
RECOG.AreProportional := function(X, k)
    return RECOG.DecomposeKronecker(X, k);
end;



# CB is a tuple containing change of basis matrix and the dimension
#   of the geometry found; return the two tensor factors of the group
#   G as matrix groups U and W */

RECOG.ConstructTensorFactors := function (G, CBTup)
local U, W, CB, DimU, F, gens, newgens, flag, Matrices, u, w, matU, matW;

    CB := CBTup[1];
    DimU := CBTup[2];

    F := G.fld;
    gens := G.gens;
    newgens := List(gens, x -> x^CB);
    if Size(gens) = 0 then
        newgens := [One(G.group)];
    fi;

    flag := RECOG.AreProportional(gens, DimU);
    Matrices := flag[2];
    flag := flag[1];

    u := NumberRows(Matrices[1][1]);
    w := NumberRows(Matrices[1][2]);

    matU := [1..Size(Matrices)];
    matW := [1..Size(Matrices)];
    matU := List(matU, x-> Matrices[x][1]);
    matW := List(matW, x-> Matrices[x][2]);
    U := GroupByGenerators(matU);
    W := GroupByGenerators(matW);

    return [U, W];

end;



RECOG.SetTypes := function(G)
local T, basis, invbasis, dim1, dim2, d, F, gens, U, W, matrices, Result;

    if not(G.IsTensorProduct) then
        return;
    fi;

    T := RECOG.TensorFactors(G);
    if not(IsMatrixGroup(G.group)) then
        return;
    fi;
    basis := G.TensorBasis;
    dim1 := Dimension(T[1]); 
    dim2 := Dimension(T[2]);
    d := G.d; 
    F := G.fld;
    matrices := G.gens;
    invbasis := basis^-1;
    gens := G.gens;
    if RECOG.AreProportional(List(matrices,m->m^invbasis), dim1) then
        Result := [invbasis, dim1];
    elif RECOG.AreProportional(List(matrices,m->m^invbasis), dim2) then
        Result := [invbasis, dim2];
    else
        Error("Error in Tensor");
    fi;
    RECOG.SetTensorBasis(G, invbasis);
    U := RECOG.ConstructTensorFactors (G, Result);
    W := U[2];
    U := U[1];
    RECOG.SetTensorFactors(G, [U, W]);

end;



# G, NonNegativeSolution: Factors := [], Fast := false, RandomElements := 25
RECOG.IsTensorMain := function (G, NonNegativeSolution, Factors, Fast, RandomElements)
local factors, fast, NmrTries, flag, gens, d, F, list, Status, Result, U, W, CB;

    factors := Factors;
    fast := Fast;
    NmrTries := RandomElements;

    flag := RECOG.TensorProductFlag(G);

    if flag <> "unknown" then
        return flag;
    fi;

    if IsMatrixGroup(G) then
        #SetGenerators (G, GroupGenerators (G));
        gens := GeneratorsOfGroup(G);
    #elif Type (G) eq ModGrp then
    #    SetGenerators (G, GroupGenerators (Group (G)));
    else
        Error("IsTensor expects a group or a G-module");
    fi;

    d := Degree(gens[1]);
    F := FieldOfMatrixList([gens]);
    Print("Tensor: \nDimension = ", F ," \n Field = ", d, "\n");

    list := RECOG.TensorTest(G, NmrTries, NonNegativeSolution, factors, fast);
    Status := list[1];
    Result := list[2];

    # we may have only checked some of the possible factorisations */
    if (Size(factors) = 0) and (Status = false) then
        RECOG.SetTensorProductFlag (G, false);
    fi;

    if Status then
        CB := Result[1];
        RECOG.SetTensorProductFlag (G, true);
        RECOG.SetTensorBasis (G, CB);
        U := RECOG.ConstructTensorFactors (G, Result);
        W := U[2];
        U := U[1];
        RECOG.SetTensorFactors (G, [U, W]);
    fi;

    return Status;

end;

# Continue from here

# return partitions of set S into subsets 

#RECOG.SetPartitions := function (SS)
#local S, Q, P, X;

#    S := SS;

#    if Size(S) = 1 then 
#        return {{S}};
#    else
#        x := Random (S);
#        Exclude (~S, x);
#        P := $$(S);
#        Q := {};
#        for X in P do 
#            for T in X do 
#                Q := Q join {X diff {T} join {T join {x}}}; 
#            od;
#            Q := Q join {X join {{x}}};
#        od;
#        return Q;
#    fi;

#end;


# compute the order of m mod n 

RECOG.OrderMod := function (m, n)
local i, mm;

    if n = 1 then 
        return 0; 
    fi;
    if Gcd(m, n) = 1 then
        return 0;
    fi; 
    i := 1;
    mm := m;
    while true do
        if mm mod n = 0 then
            return i;
        fi;
        mm := mm * m;
        i := i + 1;
    od;

end;


# return the sum of the lcms of the elements of X 

RECOG.Score := function (X)
local a;

    #return &+[Lcm (SetToSequence (T)) : T in X];
    a := List(X,T->Lcm(List(T)));
    return Sum(a);

end;


RECOG.FactorisationToInteger := function (l)
local ele, tuple;

    ele := 1;
    for tuple in l do
        ele := ele * tuple[1]^tuple[2];
    od;
    return ele;

end;


# returns the least d such that GL(d, q) has an element 
#   of order n and the corresponding factorisation of n;
#   Gcd (n, q) = 1 */

RECOG.LeastLinearSemiSimple := function (n, q)
local p, f, orders, S, least, nparts, x, y, scores, i;

    p := Factors(q)[1];

    f := Collected(Factors(n));

    # for each prime-power factor of n, store the least d
    #   such that GL(d, q) has an element of this order 

    orders := Set( List(f, x -> RECOG.OrderMod(q, x[1]^(x[2]))) );

    # also need to remove divisors
    for x in orders do 
        for y in orders do 
            if (x < y) and (y mod x = 0) then 
                Remove(orders,Position(orders,x));
            fi;
        od;
    od;

    if Size(orders) = 0 then 
        return [1, 1]; 
    fi;

    S := PartitionsSet(orders);
    S := List(S);

    scores := List(S, x-> RECOG.Score(x));

    # minimise partition score subject to maximising number of parts 

    least := scores[1]; 
    nparts := Size(S[1]);
    for i in [2..Size(scores)] do 
        if (scores[i] <= least) and (Size(S[i]) > nparts) then 
            least := scores[i];
            nparts := Size(S[i]);
        fi;
    od;

    return [least, nparts];

end;


RECOG.LeastProjectiveSemiSimple := function (n, q)
local u, m;

    if Gcd(n, q) <> 1 then 
        return false; 
    fi;

    if n = 1 then 
        return 1; 
    fi;

    u := RECOG.LeastLinearSemiSimple (n, q);
    m := u[2];
    u := u[1];

    if m > 1 then 
        return u; 
    fi;

    if (((q^u - 1)/(q - 1)) mod n) = 0 then 
        return u; 
    fi;

    return u + 1;

end;


# find smallest d such that PGL(d, q) can contain an element 
#   of projective order n 

RECOG.LeastProjective := function (n, q)
local p, f, primes, index, alpha, factor, m;

    # write n = p^alpha * m 

    p := Factors(q)[1];

    # find p'-part of projective order n 

    f := Collected(Factors(n));
    primes := List(f, x -> x[1]);

    index := Position(primes, p);
    if index > 0 then 
        alpha := f[index][2];
        factor := 1 + p^(alpha - 1);
        Remove(f, Position(f,[p,alpha]));
    else 
        alpha := 0;
        factor := 1;
    fi;

    # p'-part of projective order 
    m := RECOG.FactorizationToInteger(f);

    if alpha = 0 then 
        return RECOG.LeastProjectiveSemiSimple(m, q);
    elif m = 1 then 
        return factor; 
    else 
        return factor + RECOG.LeastLinearSemiSimple(m, q);
    fi;

end;

# return prime factorisation p^a * q^b * .. as sequence [p, a, q, b, ..]  

RECOG.PrimePowers := function (n)
    return Flat(Collected(Factors(n)));
end;


# take prime powers of n; compute scores for elements having 
#   these prime power orders; choose prime with largest score 
#   as best prime 

RECOG.FindBestPrime := function (n, q)
local D, Score, max, index, p, s, i;
   
    D := RECOG.PrimePowers(n);

    Score := [1..(Size(D)/2)];
    for i in [1..(Size(D)/2)] do
        Score[i] := RECOG.LeastProjective (D[2*i-1] * D[2*i], q);
    od;
    max := Maximum (Score);
    index := Position(Score, max);

    p := D[2 * (index - 1) + 1];
    s := D[2 * index];

    return [p, s];

end;


# return factorisations of n into ordered pairs 

RECOG.FactorList := function (n)
local D, s, list;

    D := DivisorsInt(n);
    s := Sqrt(n);
    list := Filtered(D,x -> x <= s);
    return List(list, x -> [x, n/x]);
end;


# find co-prime factorisations of n 

RECOG.CoPrimeFactorisations := function (n)
local L;

    # find co-prime factorisations of n 
    L := RECOG.FactorList(n);
    return Filtered(L, x-> Gcd(x[1],x[2]) = 1);
end;


# is there a co-prime factorisation of n as k * l such 
#   that Score (k * m) <= DimU and Score (l * m) <= DimW ? 

# Original input: (n, m, d, q, DimU, DimW: Limit := 10^3)
RECOG.ExistsFactorisation := function (n, m, d, q, DimU, DimW, Limit)
local P, u, y, x;

    # find co-prime factorisations of n 
    P := RECOG.CoPrimeFactorisations(n);

    Print("Tensor: Number of coprime factorisations is ", Size(P), "\n");

    if Size(P) > Limit then 
        return "unknown"; 
    fi;

    # is there is a valid co-prime factorisation of n? 
    #   -- that is, one whose components fit into each side 

    for x in P do
        Print("Tensor: Processing order factorisation ", x, "\n");
        u := List([1..2], i -> RECOG.LeastProjective(x[i] * m, q));

        y := List([1..2], i -> x[i] * m);
        Print("Tensor: Score for ", y, " = ", u, "\n"); 

        # is DimU >= u[1] and DimW >= u[2] or vice versa? 
        # EOB -- fix to include both options Nov 2012 
        if ((u[1] <= DimU) and (u[2] <= DimW)) or ((u[1] <= DimW) and (u[2] <= DimU)) then 
            return true;
        fi;
    od;

    return false;
end;

# can an element g of order n rule out possible tensor 
#   factorisation DimU x DimW of a subgroup of GL (d, q)? 
#   TestedPrimes records the prime order elements obtained 
#   as powers of g which are not projectivities

RECOG.PossibleFactorisation := function (G, g, nn, d, q, DimU, DimW, list, TestedPrimes)
local n, m, Primes, p, s, h, Result, CB, D, flag;

    n := nn; 
    m := 1; 
    Primes := TestedPrimes; 

    flag := RECOG.ExistsFactorisation (n, m, d, q, DimU, DimW, 10^3);
    if flag = "unknown" then 
        return ["unknown", "unknown"];   
    fi;

    while flag do 
        p := RECOG.FindBestPrime (n, q);
        s := p[2];
        p := p[1];

        h := g^((m * n)/p);
        Print("Tensor: Projective order of possible scalar element is ", ProjectiveOrder(h), "\n"); 

        # Next line was not commented by me
        # Result, T := SmashElement (G, h);

        if not(h in Primes) then 
            # D:= Set (&cat List);
            D := Set (list);
            # TODO: Implement next line
            #Result := IsMatrixProjectivity(G, h, D, Result, CB);
            CB := Result[2];
            Result := Result[1];
            if Result then 
                return [CB, Primes]; 
            fi;
            if Result = "unknown" then 
                return ["unknown", Primes]; 
            fi;
            Add(Primes, h);
        fi;

        # we can now conclude that if there is such a tensor decomposition, 
        # then an element of order m acts as a non-scalar on both factors 
        n := n/(p^s); 
        m := m * p^s;
        Print("Tensor: n is now ", n, " m is now ",m, "\n");

        flag := RECOG.ExistsFactorisation (n, m, d, q, DimU, DimW, 10^3);
    od;

    return [flag, Primes];
   
end;



# generate random elements and try to decide whether an element 
#   of projective order n rules out any possible tensor factorisation
#   of a subgroup of GL (d, q) */

# Original input: (G, N, ~List, ~Record, ~Result) 
RECOG.OrderTest := function(G, N, list, Record, Result) 
local F, d, q, NmrElts, Tested, TestedPrimes, P, MinScore, n, g, u, w, i, f;

    F := G.fld;
    d := G.d;
    q := Size(F);

    Result := false;
    NmrElts := 0; 
    Record := []; 
    Tested := [];

    TestedPrimes := Set([]);

    # generate N random elements and compute their scores 
    # P := Internal_RandomProcess(G);
    P := [1..N];
    i := 1;
    while i <= N do
        P[i] := PseudoRandom(G);
        i := i + 1;
    od;
    repeat
        g := Random(P);
        NmrElts := NmrElts + 1;
        n := ProjectiveOrder(g);

        if Position (Tested, n) <> 0 then 
            continue;  
        fi;

        Print("Tensor: \nProcessing Element ", NmrElts, " of projective order ", n, "\n");

        # what is smallest dimension which can contain 
        #   element of projective order n? 
        MinScore := RECOG.LeastProjective(n, q);
        Append(Record, [g, n]);
        Append(Tested, n);

        # now consider each possible factorisation of d as u x w
        #   and decide whether such a factorisation of d is compatible 
        #   with an element of projective order n */

        for f in list do
            u := f[1]; 
            w := f[2];
            Print("Tensor: \nConsider dimension factorisation u = ",u, "  w = ", w, "\n");

            # does the element fit into each factor? 
            if (MinScore <= u) and (MinScore <= w) then 
                Print("Tensor: Element of projective order ", n, " fits into both factors\n");
                # then the element fits into all other factors as well 
                break;
            else 
                # the element doesn't fit into both factors; 
                #   however, there may exist a coprime factorisation; 
                #   we may also be able to conclude that the element can't 
                #   act in desired manner by calls to IsProjectivity 

                Result := RECOG.PossibleFactorisation(G, g, n, d, q, u, w, list, TestedPrimes); 
                TestedPrimes := Result[2];
                Result := Result[1];

                # may have found a tensor decomposition 
                if Size(Result) = 2 then
                    return;
                    # or ruled out a possible decomposition 
                elif Result = false then 
                    Print("Tensor: No valid score exists for dimension factorisation ", f);
                    Remove(list, Position(list,f));
                elif Result = "unknown" then
                    TestedPrimes := Set([]); 
                    break; 
                fi;
            fi;
        od;
    until (Size(List) = 0) or (NmrElts >= N) or (Result);

    return [list, Record, Result];
end;


# TODO: Continue here

# find tensor product of polynomials f and g 

RECOG.PolynomialTensorProduct := function(f, g)

   return CharacteristicPolynomial(TensorProduct(CompanionMatrix(f), CompanionMatrix(g)));

end;

# take some power of g, an element of (projective) order n 
#   to obtain an element of (projective) order at most Limit 

RECOG.PowerOfSmallOrder := function (g, n, Limit)
local powers, newg, f, power;

    if (n = 1) or IsPrime(n) then 
        return g; 
    fi;

    f := Collected(Factors(n));
    powers := List(f, x -> (x[1]^x[2]));
    powers := Filtered(powers, x -> x <= Limit);

    if Size(powers) > 0 then 
        power := Random(powers);
        newg := g^(n/power);
    else
        newg := g^(n/f[1][1]);
    fi;

    return newg;
   
end;

# use the inherent symmetry of a left-hand factor to write 
#   down permutations to reduce the number of possible solutions 
   
RECOG.ApplySymmetry := function (F, n, PolyBasis) 
local q, factor, omega, lambda, image, p, Perms, PR, f;

    q := Size(F);
    factor := Gcd(q - 1, n);

    if factor = 1 then 
        return []; 
    fi;

    omega := PrimitiveElement(F);
    lambda := omega^((q - 1)/factor);

    PR := GroupByGenerators(PolyBasis);
    f := GeneratorsOfGroup(PR)[1] - lambda;

    image := List([1..Size(PolyBasis)], i -> Position(PolyBasis, TensorProduct(PolyBasis[i], f)));
    # TODO: next line?
    #image cat := [Size(PolyBasis) + 1];

    p := Subgroup(SymmetricGroup (Size(PolyBasis) + 1), image);
    Perms := List(Reversed([1..(Order(p) - 1)]), i -> (p^i) );

    return Perms;

end;

# P is the list of permutations, u is one possible left-hand side; 
#   if some image of u under an element of P occurs later in an 
#   ordering, we don't need to process u 
   
RECOG.ProcessVector := function (P, u, lenu)
local i, v, Im;
   
    i := 1; 
    repeat 
        v := P[i];
        Im := List([1..lenu], j -> [u[v[j]]]);
        if Im > u then 
            return false; 
        fi;
        i := i + 1;
    until i > Size(P);

    return true;

end;

# given sequence of polynomials, some product of which is f,
#   find which exponents occur in f 

RECOG.ExponentsOfFactors := function (R, f)
local fac, exponents, i, factor, j;

    fac := Collected(Factors(f));

    exponents := List([1..Size(R)], i -> 0);

    for i in [1..Size(fac)] do
        factor := fac[i];
        j := Position(R, factor[1]);
        exponents[j] := factor[2];
    od;

    return exponents;

end;

# setup the basis matrices and write them over the integers 

RECOG.SetupMatrices := function (Table)
local n, m, R, M, i, x, y;

    n := Size(Table[1]);
    m := Size(Table[1][1]);

    #R := RMatrixSpace(Integers (), n, m);

    M := [];
    for i in [1..Size(Table)] do
        x := Table[i];
        #y := &cat[x[j] : j in [1..#x]];
        M[i] := y;
    od;

    return M;

end;


# TODO: Implement next function
RECOG.IsConsistent := function(A, t)

end;

# TODO: Implement next function
RECOG.FindNonNegativeSolution := function(A, t)

end;


# Perms is list of possible permutations which can be 
#   used to reduce number of possible left-hand sides; 
#   M is the set of matrices; t is the right-hand side;
#   Degrees is list of degrees of the factors;
#   DimU is the degree of the u factor; 
#   build up left-hand side and solve system 

RECOG.FindFactorisation := function (Perms, M, t, Degrees, DimU, NonNegativeSolution)
local tot, n, lenm, m, x, Outstanding, LIMIT, index, flag, s, K, A, NonNegative, Resolved, zm, zs, exists, i;

    tot := 0;

    n := Size(M);
    lenm := n + 1;
    m := List([1..(n + 1)], i -> 0);
    x := 0;

    Outstanding := false; # can we settle the question for this element? 

    LIMIT := 10^5; # max number of solns to consider 
    repeat 
        index := 1;
        m[index] := m[index] + 1;
        x := x + Degree[index];

        while (index <= n) and (x > DimU) do
            x := x - m[index] * Degree[index];
            m[index] := 0;
            index := index + 1;
            m[index] := m[index] + 1;
            if index <= n then 
                x := x + Degree[index];
            fi;
        od;

        if x = DimU then 
            if (Size(Perms) = 0) or RECOG.ProcessVector(Perms, m, lenm) then 
                A := Sum(List([1..n], i -> m[i] * M[i]));
                tot := tot + 1; 
                flag := RECOG.IsConsistent(A, t); 
                s := flag[2];
                K := flag[3];
                flag := flag[1];

                if flag then 
                    Print("Tensor: A solution over Z was found after testing ", tot, " vectors of correct weight\n");
                    Print("Tensor: Kernel has dimension ", Dimension(K), "\n");
                    Resolved := true;
                    exists := false;
                    for i in [1..Degree(s)] do
                        if s[i] < 0 then
                            exists := true;
                            break;
                        fi;
                    od;
                    if exists then
                        if Dimension (K) > 0 then 
                            if NonNegativeSolution then 
                                # we should test if some translate of this solution 
                                # is non-negative; this may be very expensive 
                                Print("Tensor: Now try for a solution over N");
                                NonNegative := RECOG.FindNonNegativeSolution(A, t);
                                s := NonNegative[2];
                                NonNegative := NonNegative[1];
                            else 
                                Resolved := false;
                                # record one possible solution over Z 
                                NonNegative := false;
                                zm := m; 
                                zs := s;
                            fi; # if NonNegativeSolution 
                        else 
                            Print("Tensor: Solution is unique");
                            NonNegative := false;
                        fi; # Dimension (K) gt 0 
                    else
                        Print("Tensor: Our existing solution is over N ");
                        NonNegative := true;
                    fi; # if exists 

                    if not(Resolved) then 
                        Outstanding := true; 
                    fi;

                    if NonNegative then 
                        Print("Tensor: A solution over N found after testing", tot, "vectors of correct weight");
                        Print("Tensor: m = ", m, "s = ", s);
                        return [true, m, s, true];
                    fi;

                fi; # if flag 

            fi; # if ProcessVector 

        fi; # if x eq DimU 

    until (index > n) or (tot > LIMIT);
    # until (index gt n); 

    if tot > LIMIT then 
        Outstanding := true; 
    fi;

    if Outstanding then 
        Print("Tensor: *** Existence of non-negative solution for some u unresolved ***"); 
        return [true, zm, zs, false]; 
    fi;

    Print("Tensor: Number of vectors of correct weight tested is ", tot);

    return [false, false, false, true];

end;


# compute factors of x^n - theta 

RECOG.ListFactors := function (F, n, theta)
local x, P, R, PolyBasis, Degrees;

    x := Indeterminate(F);

    P := x^n - theta;

    R := Collected(Factors(P));
    R := Reversed(R);

    PolyBasis := List([1..Size(R)], i -> R[i][1] );
    Degrees := List([1..Size(R)], i -> Degree(R[i][1]));

    return [PolyBasis, Degrees];

end;

# compute tensor product of each element of PolyBasis1 with 2
#   and record what combination of elements of PolyBasis
#   is equal to this product  

RECOG.ComputeTensorTable := function (PolyBasis, PolyBasis1, PolyBasis2)
local T, i, tp, j;

    T := [];
    for i in [1..Size(PolyBasis1)] do
        T[i] := [];
        for j in [1..Size(PolyBasis2)] do
            tp := TensorProduct(PolyBasis1[i], PolyBasis2[j]);
            T[i][j] := RECOG.ExponentsOfFactors(PolyBasis, tp);
        od;
    od;

    return T;

end;

# f is the characteristic polynomial of an element of order n;
#   does it have a tensor factorisation with a factor of degree dimU? 

RECOG.DecideFactorisation := function (F, f, n, phi, n0, PolyBasis, dimU, t, NonNegativeSolution)
local x, E, Outstanding, theta, PolyBasis1, Degrees1, PolyBasis2, Degrees2, Table, M, Perms, found, u, v, Resolved;

    # run over theta where theta is an element of F^* / (F^*)^n  
    #   and F^* is the multiplicative group of the field 

    x := PrimitiveElement (F);
    E := List([0..(n0 - 1)], i -> x^i);

    Outstanding := false;

    for theta in E do

        PolyBasis1 := RECOG.ListFactors(F, n, theta);
        Degrees1 := PolyBasis1[2];
        PolyBasis1 := PolyBasis[1];
        PolyBasis2 := RECOG.ListFactors(F, n, phi * theta^-1);
        Degrees2 := PolyBasis2[2];
        PolyBasis2 := PolyBasis2[1];
        Table := RECOG.ComputeTensorTable(PolyBasis, PolyBasis1, PolyBasis2);
        M := RECOG.SetupMatrices(Table);

        Perms := RECOG.ApplySymmetry(F, n, PolyBasis1);
        found := RECOG.FindFactorisation(Perms, M, t, Degrees1, dimU, NonNegativeSolution);
        u := found[2];
        v := found[3];
        Resolved := found[4];
        found := found[1];
        Print("Tensor: u = ", u, " v = ", v, "\n");
        if found and Resolved then 
            return [found, u, v, Resolved]; 
        fi;

        if not(Resolved) then 
            Outstanding := true; 
        fi; 

    od;

    return [false, false, false, not Outstanding];

end;

# try to tensor factorise the characteristic polynomials
#   of N random elements of G; Outstanding records if the 
#   possible factorisation over the natural nuumbers
#   is not conclusively decided */

# Old input: G, N, ~List, ~Outstanding, NonNegativeSolution
RECOG.FactorisePolynomials := function(G, N, list, Outstanding, NonNegativeSolution)
local MaxOrder, MaxNmrFactors, F, q, Tested, NmrElts, P, i, phi, n, f, n0, found, u, v, Resolved, g, t, PolyBasis, Degrees, pair;

    MaxOrder := 40;
    MaxNmrFactors := 24;

    F := G.fld;
    q := Size(F);

    # examine tensor factorisation of characteristic polynomial 
    # TODO: Whats this? Tested := {@ @};
    Tested := Set([]);
    NmrElts := 0;

    Outstanding := false;

    P := [1..N];
    i := 1;
    while i <= N do
        P[i] := PseudoRandom(G.grp);
        i := i + 1;
    od;

    repeat
        NmrElts := NmrElts + 1;
        g := Random(P);
        #n, phi := ProjectiveOrder(g);
        n := ProjectiveOrder(g);
        phi := n[2];
        n := n[1];

        # if the order of g is too large, replace g by some power 
        if n > MaxOrder then 
            g := RECOG.PowerOfSmallOrder(g, n, MaxOrder);
            n := ProjectiveOrder(g);
            phi := n[2];
            n := n[1];
        fi;

        if n > MaxOrder then 
            continue; 
        fi;

        f := CharacteristicPolynomial(g);

        if not(f in Tested) then
            Add(Tested, f);
            n0 := Gcd(n, q - 1);

            # get factors of x^n - phi and express f as a product 
            # of its irreducible factors 

            PolyBasis := RECOG.ListFactors (F, n, phi);
            Degrees := PolyBasis[2];
            PolyBasis := PolyBasis[1];

            if Size(Degrees) > MaxNmrFactors then 
                Print("Tensor: *** Too Many Factors ***"); 
                continue; 
            fi;

            Print("Tensor: \nProjective order of element is ", n, "\n");

            t := RECOG.ExponentsOfFactors(PolyBasis, f);
            t := RECOG.RSpace(Integers (), Size(t));

            for pair in list do
                Print("Tensor: Processing dimension factorisation ", pair, "\n");
                # do we find tensor product factorisation? 
                found := RECOG.DecideFactorisation(F, f, n, phi, n0, PolyBasis, pair[1], t, NonNegativeSolution);
                u := found[2];
                v := found[3];
                Resolved := found[4];
                found := found[1];

                Print("Tensor: Resolved is ", Resolved, "\n");

                if (not found) and Resolved then 
                    Remove(list, Position(list,pair)); 
                fi;

                if not(Resolved) then 
                    Outstanding := true; 
                fi;
            od;
        fi;
    until (Size(List) = 0) or (NmrElts >= N);
end;


# TODO: Continue here


# do the projectivities generate a field? this is not a conclusive test; 
#   we simply check that they commute and that we can find a generating
#   element 

RECOG.ProjectivitiesGenerateField := function(S, order)
local G, flag, g, y, i, exists;

    for y in S do   
        exists := false;
        for i in S do
            if y*i <> i*y then
                exists := true;
                break;
            fi;
        od;
        if exists then 
            Print("Tensor: Projectivities do not commute");
            return [false, false];
        fi;
    od;

    G := GroupByGenerators(S);
    flag := RECOG.RandomElementOfOrder(G, order);
    g := flag[2];
    flag := flag[1];

    if not(flag) then 
        Print("Tensor: Didn't find element of appropriate order");
        return [false, false];
    fi;

    return [true, g];

end;

# X is a matrix, return the non-zero blocks of size k in X 

RECOG.BlocksOfMatrix := function (X, k)
local F, d, Nmr, blocks, i, j, A;

   F := FieldOfMatrixList([X]);
   d := NumberRows(X);

   Nmr := d/k;
   blocks := [];

   for i in [1..Nmr] do
      for j in [1..Nmr] do
         A := ExtractSubMatrix(X, (i - 1) * k + 1, (j - 1) * k + 1, k, k);
         if not(IsScalar(A)) then 
            Add(blocks, A); 
        fi;
      od;
   od;
 
   return blocks;

end;

# rewrite basis for P wrt N 

RECOG.ConstructNewFlat := function (N, P)
local Coeffs, B, v, F;

    F := FieldOfMatrixList(N);
    Coeffs := Basis(N);
    B := Basis(P);
    v := Sum( List([1..Size(Coeffs)], i -> List([1..Size(B)], j -> B[j] * Coeffs[i][j])));
    return VectorSpace(F,[v]);
   
end;

# can we use the potential projectivity C to give us 
#   a singular element? 

RECOG.FoundSingularElement := function (C, DimU, P)
local f, flag, factors, h, N, m;

    # compute its characteristic polynomial 
    f := CharacteristicPolynomial(C);

    # is f the DimU power of some polynomial? 
    flag := RECOG.IsPowerOfPolynomial(f, DimU);
    factors := flag[2];
    flag := flag[1];
    if flag = false then 
        return [true, true]; 
    fi;

    # is f a power of an irreducible polynomial? 
    if Size(factors) > 1 then 
        # compute generalised eigenspace of C 
        h := factors[1][1];
        N := NullspaceMat(RECOG.EvaluateImage(h, C));
        return [true, RECOG.ConstructNewFlat (N, P)];
    else 
        m := MinimalPolynomial(C);
        factors := Collected(Factors(m));
        if factors[1][2] > 1 then 
            # compute generalised eigenspace of C 
            h := factors[1][1];
            N := NullspaceMat(RECOG.EvaluateImage (h, C));
            return [true, RECOG.ConstructNewFlat (N, P)];
        else 
            return [false, false];
        fi;
    fi;
end;

# Y collection of matrices written wrt geometric basis;
#   P is a potential flat; we are searching for a point 
#   of dimension DimU 
 
RECOG.SetupBlocks := function (Y, P, DimU)
local Proj, blocks, Dim, B, i, a, b, C, Ainv, DimP, Result, N, j, exists;

    Proj := Set([]);
    blocks := [];
    DimP := Dimension(P);

    # look through DimP x DimP in matrix for each element of Y 
    #   for one with determinant 0 

    for i in [1..Size(Y)] do
        if IsScalar(Y[i]) then 
            continue; 
        fi;
        B := RECOG.BlocksOfMatrix(Y[i], DimP);
        exists := false;
        for b in B do
            if Determinant (b) = 0 then
                exists := true;
                Result := b;
                break;
            fi;
        od;
        if exists then 
            Print("Tensor: Block A has nullspace"); 
            N := NullspaceMat(Result);
            return [true, RECOG.ConstructNewFlat(N, P)];
        fi; 
        Append(blocks, B);
    od;

    # construct potential projectivities 
    for i in [1..Size(blocks)] do
        if Size(blocks)[i] = 0 then 
            Print("Tensor: #Blocks from A is 0"); 
            continue; 
        fi;
        Ainv := (blocks[i][1])^-1;
        for j in [2..Size(blocks[i])] do 
            C := blocks[i][j] * Ainv;
            if not IsScalar (C) then 
                a := RECOG.FoundSingularElement(C, DimU, P); 
                b := a[2];
                a := a[1];
                if a then 
                    return [true, b]; 
                fi;
                Add(Proj, C);
            fi;
        od;
    od;

    return [false, Proj];

end;

# search for singular element in algebra generated by collection
#   of projectivies CC 

RECOG.SearchForSingularElement := function (C, P, DimU, NmrTries)
local x, y, module, A, i, z, a, b;

    A := GroupByGenerators(C);  # to get random elements 

    i := 0;
    repeat
        x := Random (A);
        y := Random (A);
        z := x + y;
        if not IsScalar (z) then 
            a := RECOG.FoundSingularElement(z, DimU, P); 
            b := a[2];
            a := a[1];
            if a then 
                return [true, b]; 
            fi;
            Add(C, z);
        fi;
        i := i + 1;
    until i = NmrTries;

    return [false, C];

end;

# try to find singular element in algebra of projectivities 

RECOG.InvestigateMatrices := function (Y, P, DimU, NmrTries)
local DimP, flag, C;

    DimP := Dimension(P);

    flag := RECOG.SetupBlocks(Y, P, DimU);
    C := flag[2];
    flag := flag[1];

    if flag then 
        return [flag, C]; 
    fi;

    if Size(C) = 0 then 
        return [false, false]; 
    fi;

    flag := RECOG.SearchForSingularElement(C, P, DimU, NmrTries);
    C := flag[2];
    flag := flag[1];

    return [flag, C];

end;

# set up matrix whose rows are the vectors of the 
#   bases for each subspace in Sum 

RECOG.SetupMatrix := function(sum)
local S, A, basis, transform, number, a, b;

    A := [];

    for S in sum do
        basis := BasisVectors(Basis(S));
        Add(A,Matrix(basis));
    od;

    transform := [];
    number := Size(A[1]);
    for a in A do
        for b in [1..number] do
            Add(transform,a[b]);
        od;
    od;

    return transform;

end;

# find minimal set of components of Sum whose direct sum contains P;
#   U is the inclusion of P into V wrt the given basis for P and 
#   for the basis of V obtained by concatentating the given
#   bases for the direct summands 

RECOG.IdentifySubset := function (A, P, sum)
local Ainv, basis, U, DegU, k, Indices, i, j, Dim;

    Ainv := A^-1;

    basis := BasisVectors(Basis(P));
    U := List(basis, v -> v * Ainv);
    DegU := Size(U[1]);
    k := Size(sum);

    Dim := Dimension (sum[1]);
    Indices := Set([]);
    for i in [1..Size(U)] do
        for j in [1..DegU] do
            if U[i][j] <> 0 then 
                Add(Indices, (j - 1)/Dim + 1); 
                if Size(Indices) = k then 
                    return [Indices, U]; 
                fi;
            fi;
        od;
    od;

    return [Indices, U];

end;


RECOG.ComponentsOfSum:= function (P, sum, index, M)
local B;

    B := Basis(sum[index]);
    return List([1..NumberRows(M)], i -> Sum(List([1..Size(B)], j -> M[i][j] * B[j])));

end;

# extract the (index)th matrix of dimension DimP x DimP from U 

RECOG.BasisMatrix := function (P, U, index)
local DimP, m;

    DimP := Dimension(P);

    m := List([1..Size(U)], i -> List([(index-1) * DimP + 1 .. index * DimP], j -> U[i][j]));

    return m; 

end;

# construct the change of basis matrix and return it
#   together with the generators of G wrt the new basis 

RECOG.ConstructMatrices := function(G, P, Equated, A)
local k, DimP, F, K, x, i, y, j, C;
  
    k := Size(Equated);
    DimP := Dimension(P);

    F := FieldOfMatrixGroup(G);
    K := GL(NumberRows(G), F);

    x := [];
    for i in [1..Size(Equated)] do
        y := [1..Degree(Equated[i])];
        for j in [1..Degree(Equated[i])] do 
            y[j] := Sum(List([1..Degree(Equated[i][j])], k -> [Equated[i][j][k] * A[(i - 1) * DimP + k]]));
        od;
        Add(x,y);
    od;

    C := Matrix(x)^-1;

    # write down the generators of G wrt to new basis 
    return [List(GeneratorsOfGroup(G), x -> x^C), C];

end;

# # are the matrices composed of k x k blocks which differ
# #   only by scalars? if so, return the decomposition 
 
# #{Decide whether or not the matrix X is composed of k x k blocks which differ
# # only by scalars; if so, return true and the decomposition, else false}
# RECOG.IsProportional := function(X, k)
# local i, d

#     i := RECOG.AreProportional(X, k);
#     d := i[2];
#     i := i[1];
#     if i then
#         return [true, d[1]];
#     else
#         return [false, false];
#     fi;
# end;

# construct the isomorphisms from one of the equated spaces   
#   to each of the rest 

# Input: G, ~P, I, U, Sum, ~E, ~Equated
RECOG.FindIsom := function(G, P, I, U, sum, E, Equated)
local F, PG, V, StartDim, Common, fixed, Mfixed, Component, NewP, MfixedInv, M, Isom, i;

    F := G.fld;
    PG := GL(Dimension(P), F);

    V := VectorSpace(F, IdentityMat(Size(BasisVectors(Basis(P))[1]),F));

    StartDim := Dimension(P);

    # I meet E = intersection?
    Common := Intersection(I,E);

    if Size(Common) <> 0 and Size(I) <> Size(Common) then

        fixed := Representative(Common);
        Mfixed := RECOG.BasisMatrix(P, U, fixed); 

        # is Mfixed a basis for Sum[fixed]? 
        Component := RECOG.ComponentsOfSum (P, sum, fixed, Mfixed);
        NewP := Subspace(V,Component);

        if Dimension(NewP) < StartDim then 
            P := NewP;
            return [P,E,Equated];
        fi;

        MfixedInv := (Mfixed)^-1; 

        # Elements in I but not in E
        # I diff E

        for i in Difference(I,E) do 

            M := RECOG.BasisMatrix(P, U, i); 
            Component := RECOG.ComponentsOfSum(P, Sum, i, M);
            NewP := Subspace(V,Component);

            if Dimension (NewP) < StartDim then 
                P := NewP;
                return [P,E,Equated];
            fi;

            # compute the isomorphism matrix from space Mfixed to M 
            Isom := MfixedInv * M;
            Equated[i] := Equated[fixed] * Isom;
            Add(E, i);

        od; 
    fi;

    return [P,E,Equated];
     
end;


# given irreducible matrix group G and collection of subspaces of 
#   associated vector space V, write V as direct sum of subspaces of V */

# Input: Spaces, flag
RECOG.DirectSumSpaces := function(G, Spaces, flag)
local S, d, k, NmrTries, n, SumSpaces, bound, g, I, sum, D, i, count;

    S := Spaces[1];
    d := Dimension(S);
    k := Int(Size(BasisVectors(Basis(S))[1])/d);
    NmrTries := 100;
    flag := true;

    while Size(Spaces) < k do

        n := Size(Spaces);
        # Add all spaces
        # SumSpaces := &+[Spaces[i] : i in [1..n]];
        SumSpaces := [];
        for sum in Spaces do
            Append(SumSpaces, BasisVectors(Basis(sum)));
        od;
        SumSpaces := VectorSpace(G.fld,SumSpaces);

        bound := n * d;

        count := 0;
        repeat 
            count := count + 1;
            # g := RandomElement (G);
            g := PseudoRandom(G.group);
            I := S^g;
            sum := SumSpaces + I;
            D := Dimension(sum);
        until (D > bound) or (count > NmrTries);

        # do we have a submodule for G? */
        if D <= bound then
            for i in G.gens do 
                I := S^i;
                sum := SumSpaces + I;
                D := Dimension(sum);
                if D > bound then 
                    break; 
                fi;
            od;
        fi;

        # yes, so this subspace is not a flat 
        if D <= bound then 
            flag := false; 
            return [Spaces, flag]; 
        fi;

        if (D <> (n + 1) * d) then
            Spaces := [Intersection(SumSpaces, I)];
            Spaces := RECOG.DirectSumSpaces(G, Spaces, flag);
            flag := Spaces[2];
            Spaces := Spaces[1];
            return [Spaces, flag]; 
        fi;

        Add(Spaces, I);

    od;

    return [Spaces, flag];
  
end;


# flag is set false if we fail to express the underlying vector 
#   space as a direct sum of images of the contents of Spaces; 
#   this may happen if G acts reducibly or G is imprimitive */

# Input: G, ~Spaces, ~flag
RECOG.ObtainDirectSumSpaces := function(G, Spaces, flag)
local F, d, b;

    Spaces := RECOG.DirectSumSpaces(G, Spaces, flag);
    flag := Spaces[2];
    Spaces := Spaces[1];

    # have we found a submodule? 
    if not(flag) then 
        return [Spaces, flag]; 
    fi;

    F := G.fld;
    d := G.d;

    # have we found a block? 
    b := Subspace(VectorSpace (F, IdentityMat(d,F)), Spaces[1]);
    # TODO: Do we need this?
    #x := MinBlocks(G, Basis (b));
    #if IsBlockSystem(x) then 
    #    flag := false;
    #fi;

    return [Spaces, flag];
end;


# S = Sum[1];
#   S is a potential flat in a projective geometry of dimension DimU;
#   find a point in the geometry or decide that S is not a flat 

# Input: G, ~sum, DimU, ~Status, ~CB: Exact := true
RECOG.FindPoint := function(G, sum, DimU, Status, CB, Exact)
local exact, k, S, StartDim, A, F, d, Idnn, Equated, E, DimP, flag, Y, P, U, I, Result, NewP, NmrTries, g;

    exact := Exact;
    Status := false; 
    CB := "undefined"; 

    if Dimension(sum[1]) mod DimU <> 0 then 
        return [sum, Status, CB];
    fi;

    # need to equate k spaces 
    k := Size(sum);

    S := sum[1];
    StartDim := Dimension(S);

    A := RECOG.SetupMatrix(sum);

    F := G.fld;
    d := G.d;

    Idnn := One(GL(StartDim, F));
    Equated := List([1..k], i -> Idnn);

    E := Set([1]);

    repeat 

        # g := RandomElement (G);
        g := PseudoRandom(G.group);

        P := S^g;
        I := RECOG.IdentifySubset(A, P, sum);
        U := I[2];
        I := I[1];
        P := RECOG.FindIsom(G, P, I, U, sum, E, Equated);
        E := P[2];
        Equated := P[3];
        P := P[1];

        DimP := Dimension(P);

        if (DimP mod DimU) <> 0 then 
            return [sum, Status, CB]; 
        fi;

        if DimP < StartDim then 
            sum := [P];
            sum := RECOG.ObtainDirectSumSpaces(G, sum, flag);
            flag := sum[2];
            sum := sum[1];
            # if flag eq false then Status := false; return; end if;
            if not(flag) then 
                Status := "unknown"; 
                return [sum, Status, CB]; 
            fi;
            sum := RECOG.FindPoint(G, sum, DimU, Status, CB, Exact);
            Status := sum[2];
            CB := sum[3];
            sum := sum[1];
            return [sum, Status, CB];
        fi;

    until Size(E) = k;

    Print("Tensor: After setting up points in general position Dim = ", Dimension (P));

    Y := RECOG.ConstructMatrices(G, S, Equated, A);
    CB := Y[2];
    Y := Y[1];

    # are the generators of G proportional? 
    if not(exact) then 
        Status := RECOG.AreProportional(Y, DimP);
        Print("Tensor: Are matrices proportional for dim %o", DimP, "? ", Status, "\n");
    else 
        # are the generators of G proportional? 
        Status := RECOG.AreProportional(Y, DimU);
        Print("Tensor: Are matrices proportional for dim %o", DimU, "? ", Status, "\n");
        if not(Status) then 
            # are the generators of G proportional? 
            Status := RECOG.AreProportional(Y, d/DimU);
            Print("Tensor: Are matrices proportional for dim ", d/DimU, "? ", Status);
        fi;
    fi;

    if not(Status) then 
        CB := "undefined"; 
    fi;

    if Status then 
        if (DimP = DimU or DimP * DimU = d) then 
            #CB := <CB, DimP>; 
            Append(CB, DimP);
            return [sum, Status, CB]; 
        else 
            Status := "unknown";
        fi;
    elif (Dimension (P) = DimU) then 
        return [sum, Status, CB];
    fi;

    NmrTries := 100;

    Result := RECOG.InvestigateMatrices(Y, S, DimU, NmrTries);
    NewP := Result[2];
    Result := Result[1];
    if not(NewP) then 
        Status := "unknown"; 
        return [sum, Status, CB]; 
    fi;

    # did we construct a possible new flat? 
    # if (NewP) eq ModTupFld then 
    if Result then
        Print("Tensor: Found a possible new flat of dimension ", Dimension (NewP), "\n");
        if (Dimension (NewP) mod DimU) <> 0 then 
            Status := false;
            return [sum, Status, CB];
        fi;
        S := NewP;  
        sum := [S];
        sum := RECOG.ObtainDirectSumSpaces(G, sum, flag);
        flag := sum[2];
        sum := sum[1];
        # if flag eq false then Status := false; return; end if;
        if not(flag) then 
            Status := "unknown"; 
            return [sum, Status, CB]; 
        fi;
        sum := RECOG.FindPoint(G, sum, DimU, Status, CB, Exact);
        Status := sum[2];
        CB := sum[3];
        sum := sum[1];
        return [sum, Status, CB];
    elif not(Result) then 
        Print("** Unresolved case -- Probably found tensor / decomposition over extension field \n");
        Status := "unknown";
        return [sum, Status, CB]; 
        #if ProjectivitiesGenerateField (NewP, Size(F)^(DimP/DimU) - 1) then
        #    Print("** Unresolved case -- Probably found tensor / decomposition over extension field \n");
        #    Status := "unknown";
        #    return [sum, Status, CB]; 
        #else 
        #    Error("** Projectivities do not generate field **");
        #fi;
    fi;

    return [sum, Status, CB];
end;

# S is a potential flat in a projective geometry of dimension DimU;
#   find a point in the geometry or decide that S is not a flat */

# intrinsic GeneralFindPoint 
#    (G::GrpMat, ~S::., DimU::RngIntElt, ~Status::BoolElt, ~CB::. : 
#     Exact := true) 
# { This is a new intrinsic }

# Input: (G, ~S, DimU, ~Status, ~CB Exact := true)
RECOG.GeneralFindPoint := function(G, S, DimU, Status, CB, Exact)
local sum, exact, flag;

    sum := [S]; 
    exact := Exact;

    flag := true;

    sum := RECOG.ObtainDirectSumSpaces(G, sum, flag);
    flag := sum[2];
    sum := sum[1];
    if not(flag) then 
        Status := false; 
        return [sum, Status, CB]; 
    fi;

    return RECOG.FindPoint(G, sum, DimU, Status, CB, exact);

end;

# Decide if S is a point; Status is set to true if 
#   we verify S is a point 

# Input: G, ~S, DimU, ~Status, ~CB
IsPoint := function(G, S, DimU, Status, CB)
local sum, k, StartDim, Idnn, R, F, P, I, U, flag, A, Equated, g, DimP, Y;

    Status := false;

    sum := [S];
    sum := RECOG.ObtainDirectSumSpaces(G, sum, flag);
    flag := sum[2];
    sum := sum[1];
    if not(flag) then 
        Status := false; 
        return [S, Status, CB]; 
    fi;

    if Dimension(sum[1]) mod DimU <> 0 then
        return [S, Status, CB];
    fi;

    # need to equate k spaces 
    k := Size(sum);

    S := sum[1];
    StartDim := Dimension(S);

    A := RECOG.SetupMatrix(Sum);

    F := G.fld;

    Idnn := One(GL(StartDim, F));
    Equated := List([1..k], i -> Idnn);

    E := Set([1]);

    #R := Internal_RandomProcess(G);
    R := PseudoRandom(G.grp);
    #R := [1..N];
    #i := 1;
    #while i <= N do
    #    R[i] := PseudoRandom(G.grp);
    #    i := i + 1;
    #od;
    repeat 

        # g := RandomElement (G);
        g := PseudoRandom(R);

        P := S^g;
        I := RECOG.IdentifySubset(A, P, sum);
        U := I[2];
        I := I[1];

        P := RECOG.FindIsom(G, P, I, U, sum, E, Equated);
        E := P[2];
        Equated := P[3];
        P := P[1];
        DimP := Dimension(P);
        if DimP < DimU then 
            return  [S, Status, CB];    
        fi;

    until Size(E) = k;

    Y := RECOG.ConstructMatrices(G, S, Equated, A);
    CB := Y[2];
    Y := Y[1];

    # are the generators of G of the correct shape? 
    Status := RECOG.AreProportional(Y, DimU);
    Print("Tensor: Are matrices proportional? ", Status);

    return [S, Status, CB];

end;


# tests for tensor product factorisation; if tensor decomposition
#   found, then Status is true and Result is the change of basis matrix */

 RECOG.TensorTest := function(G, N, NonNegativeSolution, Factors, Fast)
 local factors, fast, Nmr, NmrTries, NmrSmash, NmrProjective, d, F, gens, q, p, Status, Result, u, x, y, list, Record, OutStanding;

    factors := Factors;
    fast := Fast;

    Nmr := 20;
    NmrTries := 25;
    NmrSmash := 4;
    NmrProjective := 4;

    gens := G.gens;
    d := G.d;
    F := G.fld;
    q := Size(F);
    p := Characteristic(F);

    # possible dimensions of tensor factors
    if factors = [] then
        list := Factors(d);
    else
        list := factors;
        list := list(List, x-> (d mod x = 0));
    fi;
    list := Remove(list, Position(list,1));
    list := Remove(list, Position(list,d));

    Print("Tensor: List of dimensions of possible tensor factorisations is \n", list);

    if Size(list) = 0 then
        Status := false;
        Result := list;
        return [Status, Result];
    fi;

    # check if the supplied matrices are already Kronecker products
    for u in DivisorsInt(d) do
        gens := G.gens;
        if Size(gens) = 0 then
            gens := [Identity (G)];
        fi;
        x := RECOG.AreProportional(gens, u);
        y := x[2];
        x := x[1];
        if x then
            Status := true;
            Result := GroupByGenerators([u]);
            return [Status,Result];
        fi;
    od;

    list := RECOG.OrderTest (G, N, list, Record, Result);
    Record := list[2];
    Result := list[3];
    list := list[1];
    if not(IsBool(Result)) and not(Result = "unknown") then
        Status := true;
        return [Status,Result];
    fi;

    Print("Tensor: \n Final list after order test is ", list, "\n");

    if Size(list) = 0 then
        Status := false;
        Result := list;
        return [Status,Result];
    fi;

    # if we have not called Smash already, then
    # Smash some elements of prime order

    #Elts := []; L := Set (&cat (list));
    #for i in [1..Minimum (Size(Record), NmrSmash)] do
    #    g := Record[i][1]; o := Record[i][2];
    #     TODO: Next big function
    #    Status, Result, Elts := ProjectivityTest (G, g, o, Elts, NmrProjective, L : Exact := factors ne []);
    #    if Status then
    #        return [Status,Result];
    #    fi;
    #    if Size(Elts) >= NmrSmash then
    #        break;
    #    fi;
    #od;

    Print("Tensor: Outstanding is ", list, "\n");

    # examine tensor factorisation of characteristic polynomial
    # FactorisePolynomials (G, N, ~list, ~OutStanding, NonNegativeSolution);
    list := RECOG.FactorisePolynomials(G, N, list, OutStanding, NonNegativeSolution);
    OutStanding := list[2];
    list := list[1];

    Print("Tensor: \nFinal list after polynomial factorisation is ", list);
    Print("Tensor: Outstanding is ", OutStanding);

    if Size(list) = 0 then
        Status := false;
        Result := list;
        return [Status, Result];
    fi;

    # we may be interested only in a fast test and do not wish
    # to invoke local test *
    if fast then
        Status := "unknown";
        Result := list;
        return [Status, Result];
    fi;

    # outstanding dimensions
    #List := Set (&cat(List));
    Print("Tensor: \nAt entry to Local, list is ", list);

    # now carry out local subgroup test
    # TODO: next big function
    #LocalTest (G, ~List, ~Result, Nmr, NmrTries: Exact := factors ne []);

    if Size(list) = 0 then
        Status := false;
        Result := [];
        return [Status, Result];
    fi;

    if IsString(Result) then
        Status := "unknown";
        Result := list;
        return [Status, Result];
    fi;

    if not(IsBool(Result)) then
        Status := true;
        return;
    fi;

    Status := Result;
    Result := list;

    return [Status, Result];

end;
