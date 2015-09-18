#############################################################################
##
##  matrix.gi          
##                                recog package
##                                                        Max Neunhoeffer
##                                                            Ákos Seress
##
##  Copyright 2005-2008 by the authors.
##  This file is free software, see license information at the end.
##
##  A collection of find homomorphism methods for matrix groups.
##
#############################################################################

SLPforElementFuncsMatrix.TrivialMatrixGroup :=
   function(ri,g)
     return StraightLineProgramNC( [ [1,0] ], 1 );
   end;

FindHomMethodsMatrix.TrivialMatrixGroup := function(ri, G)
  local g,gens;
  gens := GeneratorsOfGroup(G);
  for g in gens do
      if not(IsOne(g)) then
          return false;
      fi;
  od;
  SetSize(G,1);
  SetSize(ri,1);
  Setslpforelement(ri,SLPforElementFuncsMatrix.TrivialMatrixGroup);
  Setslptonice( ri, 
                StraightLineProgramNC([[[1,0]]],Length(GeneratorsOfGroup(G))));
  SetFilterObj(ri,IsLeaf);
  return true;
end;

RECOG.HomToScalars := function(data,el)
  return ExtractSubMatrix(el,data.poss,data.poss);
end;

FindHomMethodsMatrix.DiagonalMatrices := function(ri, G)
  local H,d,f,gens,hom,i,isscalars,j,newgens,upperleft;

  d := ri!.dimension;
  if d = 1 then
      Info(InfoRecog,2,"Found dimension 1, going to Scalars method");
      return FindHomMethodsMatrix.Scalar(ri,G);
  fi;

  gens := GeneratorsOfGroup(G);
  if not(ForAll(gens,IsDiagonalMat)) then
      return false;
  fi;

  f := ri!.field;
  isscalars := true;
  i := 1;
  while isscalars and i <= Length(gens) do
      j := 2;
      upperleft := gens[i][1][1];
      while isscalars and j <= d do
          if upperleft <> gens[i][j][j] then
              isscalars := false;
          fi;
          j := j + 1;
      od;
      i := i + 1;
  od;

  if not(isscalars) then 
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

  # Hint to the factor:
  Add(forfactor(ri).hints,rec( method := FindHomMethodsMatrix.Scalar,
                               rank := 4000, stamp := "Scalar" ),1);

  return true;
end;

#RECOG.DetWrapper := function(m)
#  local n;
#  n := ExtractSubMatrix(m,[1],[1]);
#  n[1][1] := DeterminantMat(m);
#  return n;
#end;

#FindHomMethodsMatrix.Determinant := function(ri, G)
#  local H,d,dets,gens,hom;
#  d := ri!.dimension;
#  if d = 1 then
#      Info(InfoRecog,2,"Found dimension 1, going to Scalar method");
#      return FindHomMethodsMatrix.Scalar(ri,G);
#  fi;
#
#  # check for a hint from above:
#  if IsBound(ri!.containedinsl) and ri!.containedinsl = true then
#      return false;  # will not succeed
#  fi;
#
#  gens := GeneratorsOfGroup(G);
#  dets := List(gens,RECOG.DetWrapper);
#  if ForAll(dets,IsOne) then
#      ri!.containedinsl := true;
#      return false;  # will not succeed
#  fi;
#  
#  H := GroupWithGenerators(dets);
#  hom := GroupHomomorphismByFunction(G,H,RECOG.DetWrapper);
#
#  SetHomom(ri,hom);
#
#  # Hint to the kernel:
#  forkernel(ri).containedinsl := true;
#  return true;
#end;

SLPforElementFuncsMatrix.DiscreteLog := function(ri,x)
  local log;
  log := LogFFE(x[1][1],ri!.generator);
  if log = fail then return fail; fi;
  return StraightLineProgramNC([[1,log]],1);
end;

FindHomMethodsMatrix.Scalar := function(ri, G)
  local f,gcd,generator,gens,i,l,o,pows,q,rep,slp,subset,z;
  if ri!.dimension > 1 then
      return NotApplicable;
  fi;

  # FIXME: FieldOfMatrixGroup
  f := ri!.field;
  o := One(f);
  gens := List(GeneratorsOfGroup(G),x->x[1][1]);
  subset := Filtered([1..Length(gens)],i->not(IsOne(gens[i])));
  if subset = [] then
      return FindHomMethodsMatrix.TrivialMatrixGroup(ri,G);
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
  ri!.generator := ResultOfStraightLineProgram(slp,
                                      GeneratorsOfGroup(G))[1][1][1];
  SetFilterObj(ri,IsLeaf);
  return true;
end;

RECOG.HomToDiagonalBlock := function(data,el)
  return ExtractSubMatrix(el,data.poss,data.poss);
end;

FindHomMethodsMatrix.BlockScalar := function(ri,G)
  # We assume that ri!.blocks is a list of ranges where the non-trivial
  # scalar blocks are. Note that their length does not have to sum up to 
  # the dimension, because some blocks at the end might already be trivial.
  local H,data,hom,middle,newgens,nrblocks,topblock;
  nrblocks := Length(ri!.blocks);  # this is always >= 1
  if nrblocks <= 2 then   # the factor is only one block
      # go directly to scalars in that case:
      data := rec(poss := ri!.blocks[nrblocks]);
      newgens := List(GeneratorsOfGroup(G),x->RECOG.HomToDiagonalBlock(data,x));
      H := GroupWithGenerators(newgens);
      hom := GroupHomByFuncWithData(G,H,RECOG.HomToDiagonalBlock,data);
      SetHomom(ri,hom);
      Add(forfactor(ri).hints,
          rec( method := FindHomMethodsMatrix.Scalar, rank := 2000,
               stamp := "Scalar" ),1);

      if nrblocks = 1 then     # no kernel:
          findgensNmeth(ri).method := FindKernelDoNothing;
      else   # exactly two blocks:
          findgensNmeth(ri).args[1] := 7;
          findgensNmeth(ri).args[2] := 5;
          forkernel(ri).blocks := ri!.blocks{[1]};
          # We have to go to BlockScalar with 1 block because the one block 
          # is only a part of the whole matrix:
          Add(forkernel(ri).hints,
              rec( method := FindHomMethodsMatrix.BlockScalar, rank := 2000,
                   stamp := "BlockScalar" ),1);
          Setimmediateverification(ri,true);
      fi;
      return true;
  fi;

  # We hack away at least two blocks and leave at least one:
  middle := QuoInt(nrblocks,2)+1;   # the first one taken
  topblock := ri!.blocks[nrblocks];
  data := rec(poss := [ri!.blocks[middle][1]..topblock[Length(topblock)]]);
  newgens := List(GeneratorsOfGroup(G),x->RECOG.HomToDiagonalBlock(data,x));
  H := GroupWithGenerators(newgens);
  hom := GroupHomByFuncWithData(G,H,RECOG.HomToDiagonalBlock,data);
  SetHomom(ri,hom);

  # the factor are the last few blocks:
  forfactor(ri).blocks := List(ri!.blocks{[middle..nrblocks]},
                               x->x - (ri!.blocks[middle][1]-1));
  Add(forfactor(ri).hints,
      rec( method := FindHomMethodsMatrix.BlockScalar, rank := 2000,
           stamp := "BlockScalar" ),1);

  # the kernel is the first few blocks (can be only one!):
  findgensNmeth(ri).args[1] := 3 + nrblocks;
  findgensNmeth(ri).args[2] := 5;
  forkernel(ri).blocks := ri!.blocks{[1..middle-1]};
  Add(forkernel(ri).hints,
      rec( method := FindHomMethodsMatrix.BlockScalar, rank := 2000,
           stamp := "BlockScalar" ),1);
  Setimmediateverification(ri,true);
  return true;
end;

# A helper function for base changes:

ExtendToBasisOfFullRowspace := function(m,f)
  # FIXME:
  # This function has to be improved with respect to performance:
  local i,o,v,z;
  if not(IsMutable(m)) then
      m := MutableCopyMat(m);
  fi;
  v := ZeroMutable(m[1]);
  if RankMat(m) < Length(m) then
      Error("No basis!");
      return;
  fi;
  i := 1;
  o := One(f);
  z := Zero(f);
  while Length(m) < Length(m[1]) do
      v[i] := o;
      Add(m,ShallowCopy(v));
      v[i] := z;
      if RankMat(m) < Length(m) then
          Unbind(m[Length(m)]);
      #else
      #    Print("len=",Length(m),"    \r");
      fi;
      i := i + 1;
  od;
  #Print("\n");
  return m;
end;

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

FindHomMethodsMatrix.ReducibleIso := function(ri,G)
  # First we use the MeatAxe to find an invariant subspace:
  local H,bc,compseries,f,hom,isirred,m,newgens;

  RECOG.SetPseudoRandomStamp(G,"ReducibleIso");

  if IsBound(ri!.isabsolutelyirred) and ri!.isabsolutelyirred then
      # this information is coming from above
      return false;
  fi;

  # FIXME:
  f := ri!.field;
  m := GModuleByMats(GeneratorsOfGroup(G),f);
  isirred := MTX.IsIrreducible(m);
  
  # Save the MeatAxe module for later use:
  ri!.meataxemodule := m;
  # Report enduring failure if irreducible:
  if isirred then return false; fi;
  
  # Now compute a composition series:
  compseries := MTX.BasesCompositionSeries(m);
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

  # Inform authorities that the factor can be recognised easily:
  forfactor(ri).blocks := bc.blocks;
  Add(forfactor(ri).hints,
      rec(method := FindHomMethodsMatrix.BlockLowerTriangular,
          rank := 4000,stamp := "BlockLowerTriangular"));

  return true;
end;

RECOG.HomOntoBlockDiagonal := function(data,el)
  local dim,i,m;
  dim := Length(el);
  m := ZeroMutable(el);
  for i in [1..Length(data.blocks)] do
      CopySubMatrix(el,m,data.blocks[i],data.blocks[i],
                         data.blocks[i],data.blocks[i]);
  od;
  return m;
end;

FindHomMethodsMatrix.BlockLowerTriangular := function(ri,G)
  # This is only used coming from a hint, we know what to do:
  # A base change was done to get block lower triangular shape.
  # We first do the diagonal blocks, then the lower p-part:
  local H,data,hom,newgens;
  data := rec( blocks := ri!.blocks );
  newgens := List(GeneratorsOfGroup(G),
                  x->RECOG.HomOntoBlockDiagonal(data,x));
  H := GroupWithGenerators(newgens);
  hom := GroupHomByFuncWithData(G,H,RECOG.HomOntoBlockDiagonal,data);
  SetHomom(ri,hom);

  # Now give hints downward:
  forfactor(ri).blocks := ri!.blocks;
  Add(forfactor(ri).hints, 
      rec( method := FindHomMethodsMatrix.BlockDiagonal,
           rank := 2000, stamp := "BlockDiagonal" ) );
  findgensNmeth(ri).method := FindKernelLowerLeftPGroup;
  findgensNmeth(ri).args := [];
  Add(forkernel(ri).hints,rec(method := FindHomMethodsMatrix.LowerLeftPGroup,
                              rank := 2000,stamp := "LowerLeftPGroup"));
  forkernel(ri).blocks := ri!.blocks;
  return true;
end;

FindHomMethodsMatrix.BlockDiagonal := function(ri,G)
  # This is only called by a hint, so we know what we have to do:
  # We do all the blocks projectively and thus are left with scalar blocks.
  # In the projective case we still do the same, the BlocksModScalars
  # will automatically take care of the projectiveness!
  local hom;
  hom := IdentityMapping(G);
  SetHomom(ri,hom);
  # Now give hints downward:
  forfactor(ri).blocks := ri!.blocks;
  Add(forfactor(ri).hints, 
      rec( method := FindHomMethodsProjective.BlocksModScalars,
           rank := 2000, stamp := "BlocksModScalars" ) );
  # We go to projective, although it would not matter here, because we
  # gave a working hint anyway:
  Setmethodsforfactor(ri,FindHomDbProjective);

  # the kernel:
  findgensNmeth(ri).args[1] := Length(ri!.blocks)+10;
  findgensNmeth(ri).args[2] := 7;
  # In the projective case we have to do a trick: We use an isomorphism
  # to a matrix group by multiplying things such that the last block
  # becomes an identity matrix:
  if ri!.projective then
      Add(forkernel(ri).hints,
          rec(method := FindHomMethodsProjective.BlockScalarProj,
              rank := 2000,stamp := "BlockScalarProj"));
  else
      Add(forkernel(ri).hints,rec(method := FindHomMethodsMatrix.BlockScalar,
                                  rank := 2000,stamp := "BlockScalar"));
  fi;
  forkernel(ri).blocks := ri!.blocks;
  return true;
end;

#RECOG.HomInducedOnFactor := function(data,el)
#  local dim,m;
#  dim := Length(el);
#  m := ExtractSubMatrix(el,[data.subdim+1..dim],[data.subdim+1..dim]);
#  # FIXME: no longer necessary when vectors/matrices are in place:
#  ConvertToMatrixRep(m);
#  return m;
#end;
#
#FindHomMethodsMatrix.InducedOnFactor := function(ri,G)
#  local H,dim,gens,hom,newgens,gen,data;
#  # Are we applicable?
#  if not(IsBound(ri!.subdim)) then
#      return NotApplicable;
#  fi;
#
#  # Project onto factor:
#  gens := GeneratorsOfGroup(G);
#  dim := ri!.dimension;
#  data := rec(subdim := ri!.subdim);
#  newgens := List(gens, x->RECOG.HomInducedOnFactor(data,x));
#  H := GroupWithGenerators(newgens);
#  hom := GroupHomByFuncWithData(G,H,RECOG.HomInducedOnFactor,data); 
#
#  # Now report back:
#  SetHomom(ri,hom);
#
#  # Inform authorities that the kernel can be recognised easily:
#  forkernel(ri).subdim := ri!.subdim;
#  Add(forkernel(ri).hints,rec(method := FindHomMethodsMatrix.InducedOnSubspace,
#                              rank := 2000,stamp := "InducedOnSubspace"),1);
#
#  return true;
#end;
#
RECOG.ExtractLowStuff := function(m,layer,blocks,lens,canbas)
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
  if canbas <> fail then
      return BlownUpVector(canbas,v);
  else
      return v;
  fi;
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

InstallGlobalFunction( FindKernelLowerLeftPGroup,
  function(ri)
    local b,curlay,done,el,f,i,l,lens,lvec,nothingnew,pivots,pos,ready,
          rifac,s,v,x,y;
    f := ri!.field;
    if not(IsPrimeField(f)) then
        b := CanonicalBasis(f);  # a basis over the prime field
    else
        b := fail;
    fi;
    l := [];       # here we collect generators of N
    lvec := [];    # the linear part of the layer cleaned out by the gens
    pivots := [];  # pairs of numbers indicating the layer and pivot columns
                   # this will stay strictly increasing (lexicographically)
    lens := RECOG.ComputeExtractionLayerLengths(ri!.blocks);
    if b <> fail then
        lens := lens * Length(b);
    fi;

    nothingnew := 0;   # we count until we produced 10 new generators
                       # giving no new dimension
    rifac := RIFac(ri);
    while nothingnew < 10 do
        x := RandomElm(ri,"KERNEL",true).el;
        s := SLPforElement(rifac,ImageElm( Homom(ri), x!.el ));
        y := ResultOfStraightLineProgram(s,
                 ri!.genswithmem{[ri!.nrgensH+1..Length(ri!.genswithmem)]});
        x := x^-1 * y;   # this is in the kernel

        # In the projective case we can now have matrices with an arbitrary
        # nonzero scalar on the diagonal, we get rid of it by norming.
        # Then we can go on as in the matrix group case...
        if ri!.projective and not(IsOne(x[1][1])) then
            x := (x[1][1]^-1) * x;
        fi;

        # Now clean out this vector and remember what we did:
        curlay := 1;
        v := RECOG.ExtractLowStuff(x,curlay,ri!.blocks,lens,b);
        pos := PositionNonZero(v);
        i := 1;
        done := 0*[1..Length(lvec)];   # this refers to the current gens
        ready := false;
        while not(ready) do
            # Find out where there is something left:
            while pos > Length(v) and not(ready) do
                curlay := curlay + 1;
                if curlay <= Length(lens) then
                    v := RECOG.ExtractLowStuff(x,curlay,ri!.blocks,lens,b);
                    pos := PositionNonZero(v);
                else
                    ready := true;   # x is now equal to the identity!
                fi;
            od;
            # Either there is something left in this layer or we are done
            if ready then break; fi;

            # Clean out this layer:
            while i <= Length(l) and pivots[i][1] <= curlay do
                if pivots[i][1] = curlay then
                    # we might have jumped over a layer
                    done := -v[pivots[i][2]];
                    if not(IsZero(done)) then
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
    forkernel(ri).gensNvectors := lvec;
    forkernel(ri).gensNpivots := pivots;
    forkernel(ri).blocks := ri!.blocks;
    forkernel(ri).lens := lens;
    forkernel(ri).canonicalbasis := b;
    # this is stored on the upper level:
    SetgensN(ri,l);
    ri!.leavegensNuntouched := true;
    return true;
  end );

SLPforElementFuncsMatrix.LowerLeftPGroup := function(ri,g)
  # First project and calculate the vector:
  local done,h,i,l,layer,pow;
  # Take care of the projective case:
  if ri!.projective and not(IsOne(g[1][1])) then
      g := (g[1][1]^-1) * g;
  fi;
  l := [];
  i := 1;
  for layer in [1..Length(ri!.lens)] do
      h := RECOG.ExtractLowStuff(g,layer,ri!.blocks,ri!.lens,
                                 ri!.canonicalbasis);
      while i <= Length(ri!.gensNvectors) and ri!.gensNpivots[i][1] = layer do
          done := h[ri!.gensNpivots[i][2]];
          if not(IsZero(done)) then
              AddRowVector(h,ri!.gensNvectors[i],-done);
              pow := IntFFE(done);
              g := NiceGens(ri)[i]^(-pow) * g;
              Add(l,i);
              Add(l,IntFFE(done));
          fi;
          i := i + 1;
      od;
      if not(IsZero(h)) then return fail; fi;
  od;
  if Length(l) = 0 then
      return StraightLineProgramNC([[1,0]],Length(ri!.gensNvectors));
  else
      return StraightLineProgramNC([l],Length(ri!.gensNvectors));
  fi;
end;

FindHomMethodsMatrix.LowerLeftPGroup := function(ri,G)
  local f,p;
  # Do we really have our favorite situation?
  if not(IsBound(ri!.blocks) and IsBound(ri!.lens) and 
         IsBound(ri!.canonicalbasis) and IsBound(ri!.gensNvectors) and 
         IsBound(ri!.gensNpivots)) then
      return NotApplicable;
  fi; 
  # We are done, because we can do linear algebra:
  f := ri!.field;
  p := Characteristic(f);
  SetFilterObj(ri,IsLeaf);
  Setslpforelement(ri,SLPforElementFuncsMatrix.LowerLeftPGroup);
  SetSize(ri,p^Length(ri!.gensNvectors));
  return true;
end;

FindHomMethodsMatrix.GoProjective := function(ri,G)
  local hom,q;
  Info(InfoRecog,2,"Going projective...");
  hom := IdentityMapping(G);
  SetHomom(ri,hom);
  # Now give hints downward:
  Setmethodsforfactor(ri,FindHomDbProjective);

  # the kernel:
  q := Size(ri!.field);
  findgensNmeth(ri).method := FindKernelRandom;
  findgensNmeth(ri).args := [Length(Factors(q-1))+5];
  return true;
end;
  
FindHomMethodsMatrix.KnownStabilizerChain := function(ri,G)
  local S,hom;
  if HasStoredStabilizerChain(G) then
      Info(InfoRecog,2,"Already know stabilizer chain, using 1st orbit.");
      S := StoredStabilizerChain(G);
      hom := OrbActionHomomorphism(G,S!.orb);
      SetHomom(ri,hom);
      Setmethodsforfactor(ri,FindHomDbPerm);
      forkernel(ri).StabilizerChainFromAbove := S;
      return true;
  elif IsBound(ri!.StabilizerChainFromAbove) then
      Info(InfoRecog,2,"Know stabilizer chain for super group, using base.");
      S := StabilizerChain(G,rec( Base := ri!.StabilizerChainFromAbove ));
      Info(InfoRecog,2,"Computed stabilizer chain, size=",Size(S));
      hom := OrbActionHomomorphism(G,S!.orb);
      SetHomom(ri,hom);
      Setmethodsforfactor(ri,FindHomDbPerm);
      forkernel(ri).StabilizerChainFromAbove := S;
      return true;
  fi;
  return false;
end;

#FindHomMethodsMatrix.SmallVectorSpace := function(ri,G)
#  local d,f,hom,l,method,o,q,r,v,w;
#  d := ri!.dimension;
#  f := ri!.field;
#  q := Size(f);
#  if q^d > 10000 then
#      return false;
#  fi;
#
#  # Now we will for sure find a rather short orbit:
#  # FIXME: adjust to new vector/matrix interface:
#  v := FullRowSpace(f,d);
#  repeat
#      w := Random(v);
#  until not(IsZero(w));
#  o := Orbit(G,w,OnRight);
#  hom := ActionHomomorphism(G,o,OnRight);
#
#  Info(InfoRecog,2,"Found orbit of length ",Length(o),".");
#  if Length(o) >= d then
#      l := Minimum(Length(o),3*d);
#      r := RankMat(o{[1..l]});
#      if r = d then
#          # We proved that it is an isomorphism:
#          findgensNmeth(ri).method := FindKernelDoNothing;
#          Info(InfoRecog,2,"Spans rowspace ==> found isomorphism.");
#      else 
#          Info(InfoRecog,3,"Rank of o{[1..3*d]} is ",r,".");
#      fi;
#  fi;
#
#  SetHomom(ri,hom);
#  Setmethodsforfactor(ri,FindHomDbPerm);
#  return true;
#end;
#  
#FindHomMethodsMatrix.IsomorphismPermGroup := function(ri,G)
#  SetHomom(ri,IsomorphismPermGroup(G));
#  findgensNmeth(ri).method := FindKernelDoNothing;
#  Setmethodsforfactor(ri,FindHomDbPerm);
#  return true;
#end;

AddMethod( FindHomDbMatrix, FindHomMethodsMatrix.TrivialMatrixGroup,
  3100, "TrivialMatrixGroup",
        "check whether all generators are equal to the identity matrix" );
AddMethod( FindHomDbMatrix, FindHomMethodsMatrix.DiagonalMatrices,
  1100, "DiagonalMatrices",
        "check whether all generators are multiples of the identity" );
AddMethod( FindHomDbMatrix, FindHomMethodsMatrix.KnownStabilizerChain,
  1175, "KnownStabilizerChain",
        "use an already known stabilizer chain for this group" );
AddMethod( FindHomDbMatrix, FindHomMethodsProjective.FewGensAbelian,
  1050, "FewGensAbelian",
     "if very few generators, check IsAbelian and if yes, do KnownNilpotent");
AddMethod( FindHomDbMatrix, FindHomMethodsMatrix.ReducibleIso,
  1000, "ReducibleIso",
        "use the MeatAxe to find invariant subspaces" );
AddMethod( FindHomDbMatrix, FindHomMethodsMatrix.GoProjective,
   900, "GoProjective",
        "divide out scalars and recognise projectively" );

###AddMethod( FindHomDbMatrix, FindHomMethodsMatrix.SmallVectorSpace,
###           700, "SmallVectorSpace",
###           "for small vector spaces directly compute an orbit" );

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

