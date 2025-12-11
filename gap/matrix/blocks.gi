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
#############################################################################

RECOG.HomToScalars := function(data,el)
  return ExtractSubMatrix(el,data.poss,data.poss);
end;

#! @BeginChunk DiagonalMatrices
#! This method is successful if and only if all generators of a matrix group
#! <A>G</A> are diagonal matrices. Otherwise, it returns <K>NeverApplicable</K>.
#! @EndChunk
BindRecogMethod(FindHomMethodsMatrix, "DiagonalMatrices",
"check whether all generators are diagonal matrices",
function(ri, G)
  local H,d,f,gens,hom,i,isscalars,j,newgens,upperleft;

  d := ri!.dimension;
  if d = 1 then
      Info(InfoRecog,2,"Found dimension 1, going to Scalars method");
      return FindHomMethodsMatrix.Scalar(ri,G);
  fi;

  gens := GeneratorsOfGroup(G);
  if not ForAll(gens, IsDiagonalMat) then
      return NeverApplicable;
  fi;

  f := ri!.field;
  isscalars := true;
  i := 1;
  while isscalars and i <= Length(gens) do
      j := 2;
      upperleft := gens[i][1,1];
      while isscalars and j <= d do
          if upperleft <> gens[i][j,j] then
              isscalars := false;
          fi;
          j := j + 1;
      od;
      i := i + 1;
  od;

  if not isscalars then
      # We quickly know that we want to make a balanced tree:
      ri!.blocks := List([1..d],i->[i]);
      # Note that we cannot tell the upper levels that they should better
      # have made some more generators for the kernel!

      return FindHomMethodsMatrix.BlockScalar(ri,G);
  fi;

  # Scalar matrices, so go to dimension 1:
  newgens := List(gens,x->ExtractSubMatrix(x,[1],[1]));
  H := Group(newgens);
  hom := GroupHomByFuncWithData(G,H,RECOG.HomToScalars,rec(poss := [1]));
  SetHomom(ri,hom);
  findgensNmeth(ri).method := FindKernelDoNothing;

  # Hint to the image:
  AddMethod(InitialDataForImageRecogNode(ri).hints, FindHomMethodsMatrix.Scalar, 4000);

  return Success;
end);

SLPforElementFuncsMatrix.DiscreteLog := function(ri,x)
  local log;
  log := LogFFE(x[1,1],ri!.generator);
  if log = fail then
      return fail;
  fi;
  return StraightLineProgramNC([[1,log]],1);
end;

#! @BeginChunk Scalar
#! TODO
#! @EndChunk
BindRecogMethod(FindHomMethodsMatrix, "Scalar",
"Hint TODO",
function(ri, G)
  local f,gcd,generator,gens,i,l,o,pows,q,rep,slp,subset,z;
  if ri!.dimension > 1 then
      return NotEnoughInformation;
  fi;

  # FIXME: FieldOfMatrixGroup
  f := ri!.field;
  o := One(f);
  gens := List(GeneratorsOfGroup(G),x->x[1,1]);
  subset := Filtered([1..Length(gens)], i -> not IsOne(gens[i]));
  if subset = [] then
      return FindHomMethodsGeneric.TrivialGroup(ri,G);
  fi;
  gens := gens{subset};
  q := Size(f);
  z := PrimitiveRoot(f);
  pows := [LogFFE(gens[1],z)];     # zero cannot occur!
  Add(pows,q-1);
  gcd := Gcd(Integers,pows);
  i := 2;
  while i <= Length(gens) and gcd > 1 do
      pows[i] := LogFFE(gens[i],z);
      Add(pows,q-1);
      gcd := Gcd(Integers,pows);
      i := i + 1;
  od;
  rep := GcdRepresentation(Integers,pows);
  l := [];
  for i in [1..Length(pows)-1] do
      if rep[i] <> 0 then
          Add(l,subset[i]);
          Add(l,rep[i]);
      fi;
  od;
  slp := StraightLineProgramNC([[l]],Length(GeneratorsOfGroup(G)));
  Setslptonice(ri,slp);   # this sets the nice generators
  Setslpforelement(ri,SLPforElementFuncsMatrix.DiscreteLog);
  ri!.generator := z^gcd;
  SetFilterObj(ri,IsLeaf);
  return Success;
end);


# Given a matrix `mat`, and a set of indices `poss`,
# check whether the projection to the block mat{poss}{poss}
# is valid -- that is, whether the rows and columns in
# the set poss contain only zero elements outside of the
# positions indicated by poss.
RECOG.IsDiagonalBlockOfMatrix := function(m, poss)
  local n, outside, z, i, j;
  Assert(1, NrRows(m) = NrCols(m) and IsSubset([1..NrRows(m)], poss));
  outside := Difference([1..NrRows(m)], poss);
  z := ZeroOfBaseDomain(m);
  for i in poss do
    for j in outside do
      if m[i,j] <> z or m[j,i] <> z then
        return false;
      fi;
    od;
  od;
  return true;
end;


# Homomorphism used by these recognition methods:
# - FindHomMethodsMatrix.BlockScalar
# - FindHomMethodsProjective.BlocksModScalars
RECOG.HomToDiagonalBlock := function(data,el)
  # Verify el is in the domain of definition of this homomorphism.
  # Assuming the recognition result is correct, this is of course always
  # the case if el is a group element. However, this function may also
  # be called for elements which are not contained in the group.
  # TODO: add a switch to optionally bypass this verification
  # when we definitely don't need it?
  if not RECOG.IsDiagonalBlockOfMatrix(el, data.poss) then
    return fail;
  fi;

  return ExtractSubMatrix(el,data.poss,data.poss);
end;

#! @BeginChunk BlockScalar
#! This method is only called by a hint. Alongside with the hint it gets
#! a block decomposition respected by the matrix group <A>G</A> to be recognised
#! and the promise that all diagonal blocks of all group elements
#! will only be scalar matrices. This method recursively builds a balanced tree
#! and does scalar recognition in each leaf.
#! @EndChunk
BindRecogMethod(FindHomMethodsMatrix, "BlockScalar",
"Hint TODO",
function(ri, G)
  # We assume that ri!.blocks is a list of ranges where the non-trivial
  # scalar blocks are. Note that their length does not have to sum up to
  # the dimension, because some blocks at the end might already be trivial.
  local H,data,hom,middle,newgens,nrblocks,topblock;
  nrblocks := Length(ri!.blocks);  # this is always >= 1
  if nrblocks <= 2 then   # the image is only one block
      # go directly to scalars in that case:
      data := rec(poss := ri!.blocks[nrblocks]);
      newgens := List(GeneratorsOfGroup(G),x->RECOG.HomToDiagonalBlock(data,x));
      H := GroupWithGenerators(newgens);
      hom := GroupHomByFuncWithData(G,H,RECOG.HomToDiagonalBlock,data);
      SetHomom(ri,hom);
      AddMethod(InitialDataForImageRecogNode(ri).hints, FindHomMethodsMatrix.Scalar, 2000);

      if nrblocks = 1 then     # no kernel:
          findgensNmeth(ri).method := FindKernelDoNothing;
      else   # exactly two blocks:
          # FIXME: why don't we just compute a precise set of generators of the kernel?
          # That should be easily and efficiently possible at this point, no?
          # The kernel is abelian, so we don't need to do normal closures.
          findgensNmeth(ri).method := FindKernelRandom;
          findgensNmeth(ri).args := [7];
          InitialDataForKernelRecogNode(ri).blocks := ri!.blocks{[1]};
          # We have to go to BlockScalar with 1 block because the one block
          # is only a part of the whole matrix:
          AddMethod(InitialDataForKernelRecogNode(ri).hints, FindHomMethodsMatrix.BlockScalar, 2000);
          Setimmediateverification(ri,true);
      fi;
      return Success;
  fi;

  # We hack away at least two blocks and leave at least one:
  middle := QuoInt(nrblocks,2)+1;   # the first one taken
  topblock := ri!.blocks[nrblocks];
  data := rec(poss := [ri!.blocks[middle][1]..topblock[Length(topblock)]]);
  newgens := List(GeneratorsOfGroup(G),x->RECOG.HomToDiagonalBlock(data,x));
  H := GroupWithGenerators(newgens);
  hom := GroupHomByFuncWithData(G,H,RECOG.HomToDiagonalBlock,data);
  SetHomom(ri,hom);

  # the image are the last few blocks:
  InitialDataForImageRecogNode(ri).blocks := List(ri!.blocks{[middle..nrblocks]},
                               x->x - (ri!.blocks[middle][1]-1));
  AddMethod(InitialDataForImageRecogNode(ri).hints, FindHomMethodsMatrix.BlockScalar, 2000);

  # the kernel is the first few blocks (can be only one!):
  # FIXME: why don't we just compute a precise set of generators of the kernel?
  # That should be easily and efficiently possible at this point, no?
  findgensNmeth(ri).args[1] := 3 + nrblocks;
  findgensNmeth(ri).args[2] := 5;
  InitialDataForKernelRecogNode(ri).blocks := ri!.blocks{[1..middle-1]};
  AddMethod(InitialDataForKernelRecogNode(ri).hints, FindHomMethodsMatrix.BlockScalar, 2000);
  Setimmediateverification(ri,true);
  return Success;
end);

# A helper function for base changes:
RECOG.HomDoBaseChange := function(data,el)
  return data.t*el*data.ti;
end;

RECOG.CleanRow := function( basis, vec, extend, dec)
  local c,firstnz,i,j,lc,len,lev,mo,newpiv,pivs;
  # INPUT
  # basis: record with fields
  #        pivots   : integer list of pivot columns of basis matrix
  #        vectors : matrix of basis vectors in semi echelon form
  # vec  : vector of same length as basis vectors
  # extend : boolean value indicating whether the basis will we extended
  #          note that for the greased case also the basis vectors before
  #          the new one may be changed
  # OUTPUT
  # returns decomposition of vec in the basis, if possible.
  # otherwise returns 'fail' and adds cleaned vec to basis and updates
  # pivots
  # NOTES
  # destructive in both arguments

  # Clear dec vector if given:
  if dec <> fail then
    MultRowVector(dec,Zero(dec[1]));
  fi;

  # First a little shortcut:
  firstnz := PositionNonZero(vec);
  if firstnz > Length(vec) then
      return true;
  fi;

  len := Length(basis.vectors);
  i := 1;

  for j in [i..len] do
    if basis.pivots[j] >= firstnz then
      c := vec[ basis.pivots[ j ] ];
      if not IsZero( c ) then
        if dec <> fail then
          dec[ j ] := c;
        fi;
        AddRowVector( vec, basis.vectors[ j ], -c );
      fi;
    fi;
  od;

  newpiv := PositionNonZero( vec );
  if newpiv = Length( vec ) + 1 then
    return true;
  else
    if extend then
      c := vec[newpiv]^-1;
      MultRowVector( vec, vec[ newpiv ]^-1 );
      if dec <> fail then
        dec[len+1] := c;
      fi;
      Add( basis.vectors, vec );
      Add( basis.pivots, newpiv );
    fi;
    return false;
  fi;
end;

RECOG.FindAdjustedBasis := function(l)
  # l must be a list of matrices coming from MTX.BasesCompositionSeries.
  local blocks,i,pos,seb,v;
  blocks := [];
  seb := rec( vectors := [], pivots := [] );
  pos := 1;
  for i in [2..Length(l)] do
      for v in l[i] do
          RECOG.CleanRow(seb,ShallowCopy(v),true,fail);
      od;
      Add(blocks,[pos..Length(seb.vectors)]);
      pos := Length(seb.vectors)+1;
  od;
  ConvertToMatrixRep(seb.vectors);
  return rec(base := seb.vectors, baseinv := seb.vectors^-1, blocks := blocks);
end;

#! @BeginChunk ReducibleIso
#! This method determines whether a matrix group <A>G</A> acts irreducibly.
#! If yes, then it returns <K>NeverApplicable</K>. If <A>G</A> acts reducibly then
#! a composition series of the underlying module is computed and a base
#! change is performed to write <A>G</A> in a block lower triangular form.
#! Also, the method passes a hint to the image group that it is in
#! block lower triangular form, so the image immediately can make
#! recursive calls for the actions on the diagonal blocks, and then to the
#! lower <M>p</M>-part. For the image the method
#! <Ref Subsect="BlockLowerTriangular" Style="Text"/> is used.
#! 
#! Note that this method is implemented in a way such that it can also be
#! used as a method for a projective group <A>G</A>. In that case the
#! recognition node has the <C>!.projective</C> component bound
#! to <K>true</K> and this information is passed down to image and kernel.
#! @EndChunk
BindRecogMethod(FindHomMethodsMatrix, "ReducibleIso",
"use the MeatAxe to find invariant subspaces",
# alternative comment:
#"use MeatAxe to find a composition series, do base change",
function(ri,G)
  # First we use the MeatAxe to find an invariant subspace:
  local H,bc,compseries,hom,newgens;

  RECOG.SetPseudoRandomStamp(G,"ReducibleIso");

  if IsBound(ri!.isabsolutelyirred) and ri!.isabsolutelyirred then
      # this information is coming from above
      return NeverApplicable;
  fi;

  # Report enduring failure if irreducible:
  if RECOG.IsIrreducible(ri) then
      return NeverApplicable;
  fi;

  # Now compute a composition series:
  compseries := MTX.BasesCompositionSeries(RECOG.MeataxeModule(ri));
  bc := RECOG.FindAdjustedBasis(compseries);

  Info(InfoRecog,2,"Found composition series with block sizes ",
       List(bc.blocks,Length)," (dim=",ri!.dimension,")");

  # Do the base change:
  newgens := List(GeneratorsOfGroup(G),x->bc.base*x*bc.baseinv);
  H := GroupWithGenerators(newgens);
  hom := GroupHomByFuncWithData(G,H,RECOG.HomDoBaseChange,
                                rec(t := bc.base,ti := bc.baseinv));

  # Now report back:
  SetHomom(ri,hom);
  findgensNmeth(ri).method := FindKernelDoNothing;

  # Inform authorities that the image can be recognised easily:
  InitialDataForImageRecogNode(ri).blocks := bc.blocks;
  AddMethod(InitialDataForImageRecogNode(ri).hints, FindHomMethodsMatrix.BlockLowerTriangular, 4000);

  return Success;
end);

# Given a matrix `mat` and a list of index sets `blocks`,
# verify that the matrix has block lower triangular shape
# with respect to the given blocks.
RECOG.IsBlockLowerTriangularWithBlocks := function(mat, blocks)
  local z, b, col, row;
  Assert(0, Concatenation(blocks) = [1..Length(mat)]);
  z := ZeroOfBaseDomain(mat);
  for b in blocks do
    # Verify that there are only zeros above each block
    for row in [1..b[1]-1] do
      for col in b do
        if mat[row,col] <> z then
          return false;
        fi;
      od;
    od;
  od;
  return true;
end;

# Homomorphism method used by FindHomMethodsMatrix.BlockLowerTriangular.
RECOG.HomOntoBlockDiagonal := function(data,el)
  local m, x;

  # Verify el is in the domain of definition of this homomorphism.
  # Assuming the recognition result is correct, this is of course always
  # the case if el is a group element. However, this function may also
  # be called for elements which are not contained in the group.
  if not RECOG.IsBlockLowerTriangularWithBlocks(el,data.blocks) then
    return fail;
  fi;

  m := ZeroMutable(el);
  for x in data.blocks do
    CopySubMatrix(el, m, x, x, x, x);
  od;
  return m;
end;

#! @BeginChunk BlockLowerTriangular
#! This method is only called when a hint was passed down from the method
#! <Ref Subsect="ReducibleIso" Style="Text"/>. In that case, it knows that a
#! base change to block lower triangular form has been performed. The method
#! can then immediately find a homomorphism by mapping to the diagonal blocks.
#! It sets up this homomorphism and gives hints to image and kernel. For the
#! image, the method <Ref Subsect="BlockDiagonal" Style="Text"/> is used and
#! for the kernel, the method <Ref Subsect="LowerLeftPGroup" Style="Text"/>
#! is used.
#! 
#! Note that this method is implemented in a way such that it can also be
#! used as a method for a projective group <A>G</A>. In that case the
#! recognition node has the <C>!.projective</C> component bound
#! to <K>true</K> and this information is passed down to image and kernel.
#! @EndChunk
BindRecogMethod(FindHomMethodsMatrix, "BlockLowerTriangular",
"for a group generated by block lower triangular matrices",
function(ri,G)
  # This is only used coming from a hint, we know what to do:
  # A base change was done to get block lower triangular shape.
  # We first do the diagonal blocks, then the lower p-part:
  local H,data,hom,newgens;
  data := rec( blocks := ri!.blocks );
  newgens := List(GeneratorsOfGroup(G),
                  x->RECOG.HomOntoBlockDiagonal(data,x));
  Assert(0, not fail in newgens);
  H := GroupWithGenerators(newgens);
  hom := GroupHomByFuncWithData(G,H,RECOG.HomOntoBlockDiagonal,data);
  SetHomom(ri,hom);

  # Now give hints downward:
  InitialDataForImageRecogNode(ri).blocks := ri!.blocks;
  AddMethod(InitialDataForImageRecogNode(ri).hints, FindHomMethodsMatrix.BlockDiagonal, 2000);
  findgensNmeth(ri).method := RECOG.FindKernelLowerLeftPGroup;
  findgensNmeth(ri).args := [];
  AddMethod(InitialDataForKernelRecogNode(ri).hints, FindHomMethodsMatrix.LowerLeftPGroup, 2000);
  InitialDataForKernelRecogNode(ri).blocks := ri!.blocks;
  return Success;
end);

#! @BeginChunk BlockDiagonal
#! This method is only called when a hint was passed down from the method
#! <Ref Subsect="BlockLowerTriangular" Style="Text"/>.
#! In that case, it knows that the group is in block diagonal form.
#! The method is used both in the matrix- and the projective case.
#! 
#! The method immediately delegates to projective methods handling
#! all the diagonal blocks projectively. This is done by giving a hint
#! to the image to use the method
#! <Ref Subsect="BlocksModScalars" Style="Text"/>.
#! The method for the kernel then has to deal with only scalar blocks,
#! either projectively or with scalars, which is again done by giving a hint
#! to either use <Ref Subsect="BlockScalar" Style="Text"/> or
#! <Ref Subsect="BlockScalarProj" Style="Text"/> respectively.
#! 
#! Note that this method is implemented in a way such that it can also be
#! used as a method for a projective group <A>G</A>. In that case the
#! recognition node has the <C>!.projective</C> component bound
#! to <K>true</K> and this information is passed down to image and kernel.
#! @EndChunk
BindRecogMethod(FindHomMethodsMatrix, "BlockDiagonal",
"for groups generated by block diagonal matrices",
function(ri,G)
  # This is only called by a hint, so we know what we have to do:
  # We do all the blocks projectively and thus are left with scalar blocks.
  # In the projective case we still do the same, the BlocksModScalars
  # will automatically take care of the projectiveness!
  SetHomom(ri, IdentityMapping(G));
  # Now give hints downward:
  InitialDataForImageRecogNode(ri).blocks := ri!.blocks;
  AddMethod(InitialDataForImageRecogNode(ri).hints, FindHomMethodsProjective.BlocksModScalars, 2000);
  # We go to projective, although it would not matter here, because we
  # gave a working hint anyway:
  Setmethodsforimage(ri,FindHomDbProjective);

  # the kernel:
  # The kernel is abelian, so we don't need to do normal closures.
  findgensNmeth(ri).method := FindKernelRandom;
  findgensNmeth(ri).args := [Length(ri!.blocks)+10];
  # In the projective case we have to do a trick: We use an isomorphism
  # to a matrix group by multiplying things such that the last block
  # becomes an identity matrix:
  if ri!.projective then
      AddMethod(InitialDataForKernelRecogNode(ri).hints,
                FindHomMethodsProjective.BlockScalarProj,
                2000);
  else
      AddMethod(InitialDataForKernelRecogNode(ri).hints, FindHomMethodsMatrix.BlockScalar, 2000);
  fi;
  InitialDataForKernelRecogNode(ri).blocks := ri!.blocks;
  Setimmediateverification(ri, true);
  return Success;
end);

RECOG.ExtractLowStuff := function(m,layer,blocks,lens,basisOfFieldExtension)
  local block,i,j,k,l,pos,v,what,where;
  v := ZeroVector(lens[layer],m[1]);
  pos := 0;
  i := layer+1;
  l := Length(blocks);
  # Extract the blocks with block coordinates (i,1)..(l,l-i+1):
  for j in [1..l-i+1] do
      block := [j+i-1,j];
      what := blocks[block[2]];
      for k in blocks[block[1]] do
          where := [pos+1..pos+Length(what)];
          CopySubVector(m[k],v,what,where);
          pos := pos + Length(what);
      od;
  od;
  if basisOfFieldExtension <> fail then
      # needed because we assume for example in
      # SLPforElementFuncsMatrix.LowerLeftPGroup that we work
      # over a field of order p (not a p power)
      return BlownUpVector(basisOfFieldExtension, v);
  fi;
  return v;
end;

RECOG.ComputeExtractionLayerLengths := function(blocks)
  local block,i,j,l,len,lens;
  lens := [];
  l := Length(blocks);
  for i in [2..Length(blocks)] do
      len := 0;
      for j in [1..l-i+1] do
          block := [j+i-1,j];
          len := len + Length(blocks[block[1]]) * Length(blocks[block[2]]);
      od;
      Add(lens,len);
  od;
  return lens;
end;

RECOG.FindKernelLowerLeftPGroup := function(ri)
    local basisOfFieldExtension,curlay,done,el,f,i,l,lens,lvec,nothingnew,pivots,pos,ready,
          rifac,s,v,x,y;

    Info(InfoRecog, 2, "Running FindKernelLowerLeftPGroup...");
    f := ri!.field;
    l := [];       # here we collect generators of N
    lvec := [];    # the linear part of the layer cleaned out by the gens
    pivots := [];  # pairs of numbers indicating the layer and pivot columns
                   # this will stay strictly increasing (lexicographically)
    lens := RECOG.ComputeExtractionLayerLengths(ri!.blocks);

    if not IsPrimeField(f) then
        basisOfFieldExtension := CanonicalBasis(f);  # a basis over the prime field
        lens := lens * Length(basisOfFieldExtension);
    else
        basisOfFieldExtension := fail;
    fi;

    nothingnew := 0;   # we count until we produced 10 new generators
                       # giving no new dimension
    rifac := ImageRecogNode(ri);
    while nothingnew < 10 do
        x := RandomElm(ri,"KERNEL",true).el;
        Assert(2, ValidateHomomInput(ri, x));
        s := SLPforElement(rifac,ImageElm( Homom(ri), x!.el ));
        y := ResultOfStraightLineProgram(s, ri!.pregensfacwithmem);
        x := x^-1 * y;   # this is in the kernel

        # Now clean out this vector and remember what we did:
        curlay := 1;
        v := RECOG.ExtractLowStuff(x,curlay,ri!.blocks,lens,basisOfFieldExtension);
        pos := PositionNonZero(v);
        i := 1;
        done := 0*[1..Length(lvec)];   # this refers to the current gens
        ready := false;
        while not ready do
            # Find out where there is something left:
            while pos > Length(v) do
                curlay := curlay + 1;
                if curlay <= Length(lens) then
                    v := RECOG.ExtractLowStuff(x,curlay,ri!.blocks,lens,basisOfFieldExtension);
                    pos := PositionNonZero(v);
                else
                    ready := true;   # x is now equal to the identity!
                    break;
                fi;
            od;
            # Either there is something left in this layer or we are done
            if ready then break; fi;

            # Clean out this layer:
            while i <= Length(l) and pivots[i][1] <= curlay do
                if pivots[i][1] = curlay then
                    # we might have jumped over a layer
                    done := -v[pivots[i][2]];
                    if not IsZero(done) then
                        AddRowVector(v,lvec[i],done);
                        x := x * l[i]^IntFFE(done);
                    fi;
                fi;
                i := i + 1;
            od;
            pos := PositionNonZero(v);
            if pos <= Length(v) then  # something left here!
                ready := true;
            fi;
        od;
        # Now we have cleaned out x until one of the following happened:
        #   x is the identity (<=> curlay > Length(lens))
        #   x has been cleaned up to some layer and is not yet zero
        #     in that layer (<=> pos <= Length(v))
        #     then a power of x will be a new generator in that layer and
        #     has to be added in position i in the list of generators
        if curlay <= Length(lens) then   # a new generator
            # Now find a new pivot:
            el := v[pos]^-1;
            MultRowVector(v,el);
            x := x ^ IntFFE(el);
            Add(l,x,i);
            Add(lvec,v,i);
            Add(pivots,[curlay,pos],i);
            nothingnew := 0;
        else
            nothingnew := nothingnew + 1;
        fi;
    od;

    # Now make sure those things get handed down to the kernel:
    InitialDataForKernelRecogNode(ri).gensNvectors := lvec;
    InitialDataForKernelRecogNode(ri).gensNpivots := pivots;
    InitialDataForKernelRecogNode(ri).blocks := ri!.blocks;
    InitialDataForKernelRecogNode(ri).lens := lens;
    InitialDataForKernelRecogNode(ri).basisOfFieldExtension := basisOfFieldExtension;
    # this is stored on the upper level:
    SetgensN(ri,l);
    ri!.leavegensNuntouched := true;
    return true;
end;

# computes a straight line program (SLP) for an element <g> of a p-group
# described by <ri> (that corresponds to a matrix group consisting of lower
# triangular matrices).
# The SLP is constructed by using matrices forming a pcgs (polycyclic
# generating sequence) to cancel out the
# entries in <g>. The coefficents of the process create the SLP.
# TODO Max H. wants to rewrite the code to work row-by-row
# instead of blockwise; that should result in both simpler and faster code.
SLPforElementFuncsMatrix.LowerLeftPGroup := function(ri,g)
  # First project and calculate the vector:
  local done,h,i,l,layer,pow;
  # Take care of the projective case:
  if ri!.projective and not IsOne(g[1,1]) then
      g := (g[1,1]^-1) * g;
  fi;
  l := [];
  i := 1;
  for layer in [1..Length(ri!.lens)] do
      h := RECOG.ExtractLowStuff(g,layer,ri!.blocks,ri!.lens,
                                 ri!.basisOfFieldExtension);
      while i <= Length(ri!.gensNvectors) and ri!.gensNpivots[i][1] = layer do
          done := h[ri!.gensNpivots[i][2]];
          if not IsZero(done) then
              AddRowVector(h,ri!.gensNvectors[i],-done);
              pow := IntFFE(done);
              g := NiceGens(ri)[i]^(-pow) * g;
              Add(l,i);
              Add(l,IntFFE(done));
          fi;
          i := i + 1;
      od;
      if not IsZero(h) then
          return fail;
      fi;
  od;
  if Length(l) = 0 then
      l := [1, 0];
  fi;
  return StraightLineProgramNC([l], Length(ri!.gensNvectors));
end;

#! @BeginChunk LowerLeftPGroup
#! This method is only called by a hint from <Ref Subsect="BlockLowerTriangular" Style="Text"/>
#! as the kernel of the homomorphism mapping to the diagonal blocks.
#! The method uses the fact that this kernel is a <M>p</M>-group where
#! <M>p</M> is the characteristic of the underlying field. It exploits
#! this fact and uses this special structure to find nice generators
#! and a method to express group elements in terms of these.
#! @EndChunk
BindRecogMethod(FindHomMethodsMatrix, "LowerLeftPGroup",
"Hint TODO",
function(ri,G)
  local f,p;
  # Do we really have our favorite situation?
  if not (IsBound(ri!.blocks) and
          IsBound(ri!.lens) and
          IsBound(ri!.basisOfFieldExtension) and
          IsBound(ri!.gensNvectors) and
          IsBound(ri!.gensNpivots)) then
      return NotEnoughInformation;
  fi;
  # We are done, because we can do linear algebra:
  f := ri!.field;
  p := Characteristic(f);
  SetFilterObj(ri,IsLeaf);
  Setslpforelement(ri,SLPforElementFuncsMatrix.LowerLeftPGroup);
  SetSize(ri,p^Length(ri!.gensNvectors));
  return Success;
end);
