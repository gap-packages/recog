#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This files's authors include Max Neunhöffer, Alice Niemeyer, Ákos Seress.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
##
##  Find an imprimitive action of a matrix group.
##  This should better be (and is now) called "LowIndex".
##
#############################################################################

#
#  Test if the module hm already has a submodule with a
#  short enough orbit.
#  Note: We can tweak what ``short enough" means. I set it to 4d,
#  but if we make it smaller it will speed up the code.
#

RECOG.IndexMaxSub := function( hm, grp, d )
    # Call this function only with a reducible module hm!
    local dim,dimnew,f,i,lastorb,lastsub,orb,sp,spnew,sub,subdim;

    # Here is the invariant subspace
    sub := MTX.ProperSubmoduleBasis(hm);
    sub := MutableCopyMat( sub );  # make mutable copy
    # FIXME: this will be unnecessary:
    ConvertToMatrixRep(sub,hm.field);
    lastsub := fail;
    lastorb := fail;
    repeat
        TriangulizeMat(sub); # Find Hermite Normal Form
        orb := Orb(grp,sub,OnSubspacesByCanonicalBasis,
                   rec(storenumbers := true, hashlen := NextPrimeInt(8*d)));
        Enumerate(orb,4*d);
        if not IsClosed(orb) then
            Info(InfoRecog,2,"Did not find nice orbit.");
            if lastsub = fail then
                return fail;
            fi;
            return rec( orb := lastorb,
                        hom := OrbActionHomomorphism(grp,lastorb) );
        fi;
        Info(InfoRecog,2,"Found orbit of length ",Length(orb),
             " of subspaces of dimension ",Length(orb[1]),".");
        subdim := Length(orb[1]);
        if subdim * Length(orb) = d or    # have block system!
           subdim = 1 then                # no hope in this case
            return
                rec(orb := orb,
                    hom := OrbActionHomomorphism(grp,orb));
        fi;
        # we try intersecting the subspaces in the orbit:
        Info(InfoRecog,2,"Calculating intersections...");
        f := hm.field;
        sp := VectorSpace(f,orb[1]);
        dim := Dimension(sp);
        for i in [2..Length(orb)] do
            spnew := Intersection(sp,VectorSpace(f,orb[i]));
            dimnew := Dimension(spnew);
            if dimnew > 0 and dimnew < dim then
                sp := spnew;
                dim := dimnew;
            fi;
        od;
        Info(InfoRecog,2,"Got subspace of dimension ",Dimension(sp));
        if dim = Length(sub) then   # we got nothing new
            Info(InfoRecog,2,"That we already knew, giving up.");
            return
                rec(orb := orb,
                    hom := OrbActionHomomorphism(grp,orb));
        fi;
        lastsub := sub;
        lastorb := orb;
        sub := MutableCopyMat(AsList(Basis(sp)));
        # FIXME: This will vanish:
        ConvertToMatrixRep(sub,hm.field);
    until false;
end;

RECOG.SmallHomomorphicImageProjectiveGroup := function ( grp )

    local hm, findred, ans, fld, d, i, gens;

    fld := DefaultFieldOfMatrixGroup(grp);
    d := DimensionOfMatrixGroup(grp);

    findred := function( gens )
      local hm,i,j,res;
      i := Length(gens)+1;
      for j in [1..d] do
          gens[i] := PseudoRandom(grp);
          hm := GModuleByMats(gens,fld);
          if not MTX.IsIrreducible(hm) then
              res := RECOG.IndexMaxSub( hm, grp, d );
              if res <> fail then
                  return [res, gens];
              fi;
              if i < LogInt(d,2) then
                  res := findred(gens);
                  if res = false then
                      return false;
                  fi;
                  if res <> fail then
                      return res;
                  fi;
              fi;
          fi;
      od;
      return false;   # go out all the way without success
    end;

    Info(InfoRecog,2,"LowIndex: Trying 10 first elements...");
    for i in [1..10] do   # this is just heuristics!
        gens := [PseudoRandom(grp)];
        hm := GModuleByMats(gens,fld);
        if not MTX.IsIrreducible(hm) then
            ans := findred( gens );
            if ans <> fail and ans <> false then
                return ans;
            fi;
        fi;
        if InfoLevel(InfoRecog) >= 2 then Print(".\c"); fi;
    od;
    if InfoLevel(InfoRecog) >= 2 then Print("\n"); fi;

    return fail;
end;


#! @BeginChunk LowIndex
#! This method is designed for the handling of the Aschbacher class C2
#! (stabiliser of a decomposition of the underlying vector space), but may
#! succeed on other types of input as well. Given <A>G</A> <M> \le PGL(d,q)</M>,
#! the output is either the permutation action of <A>G</A> on a short
#! orbit of subspaces or <K>fail</K>. In the current setup, <Q>short orbit</Q>
#! is defined to have length at most <M>4d</M>.
#! @EndChunk
BindRecogMethod(FindHomMethodsProjective, "LowIndex",
"find an (imprimitive) action on subspaces",
function(ri,G)
  local res;
  RECOG.SetPseudoRandomStamp(G,"LowIndex");
  res := RECOG.SmallHomomorphicImageProjectiveGroup(G);
  if res = fail then
      return fail; # FIXME: fail = TemporaryFailure here really correct?
  else
      res := res[1];
      # Now distinguish between a block system and just an orbit:
      if Length(res.orb) * Length(res.orb[1]) <> ri!.dimension then
          Info(InfoRecog,2,"Found orbit of length ",Length(res.orb),
               " - not a block system.");
      else
          Info(InfoRecog,2,"Found block system with ",Length(res.orb),
               " blocks.");
          # A block system: We do a base change isomorphism:
          InitialDataForKernelRecogNode(ri).t := Concatenation(res.orb);
          InitialDataForKernelRecogNode(ri).blocksize := Length(res.orb[1]);
          AddMethod(InitialDataForKernelRecogNode(ri).hints, FindHomMethodsProjective.DoBaseChangeForBlocks, 2000);
          Setimmediateverification(ri,true);
          findgensNmeth(ri).args[1] := Length(res.orb)+3;
          findgensNmeth(ri).args[2] := 5;
      fi;

      # we are done, report the hom:
      SetHomom(ri,res.hom);
      Setmethodsforimage(ri,FindHomDbPerm);

      return Success;
  fi;
end);

#! @BeginChunk DoBaseChangeForBlocks
#! TODO
#! @EndChunk
BindRecogMethod(FindHomMethodsProjective, "DoBaseChangeForBlocks",
"Hint TODO",
function(ri,G)
  # Do the base change:
  local H,iso,newgens,ti;

  ti := ri!.t^-1;
  newgens := List(GeneratorsOfGroup(G),x->ri!.t*x*ti);
  H := GroupWithGenerators(newgens);
  iso := GroupHomByFuncWithData(G,H,RECOG.HomDoBaseChange,
                                rec(t := ri!.t,ti := ti));

  # Now report back:
  SetHomom(ri,iso);
  findgensNmeth(ri).method := FindKernelDoNothing;

  # Inform authorities that the image can be recognised easily:
  InitialDataForImageRecogNode(ri).blocksize := ri!.blocksize;
  AddMethod(InitialDataForImageRecogNode(ri).hints, FindHomMethodsProjective.Blocks, 2000);

  return Success;
end);

#! @BeginChunk Blocks
#! TODO
#! @EndChunk
BindRecogMethod(FindHomMethodsProjective, "Blocks",
"Hint TODO",
function(ri,G)
  # Here we use BlocksModScalars and then get a kernel of scalar blocks
  # altogether mod scalars.
  local blocks,d,hom,i;
  hom := IdentityMapping(G);
  SetHomom(ri,hom);
  blocks := [];
  d := ri!.dimension;
  for i in [1..d/ri!.blocksize] do
      Add(blocks,[(i-1)*ri!.blocksize+1..i*ri!.blocksize]);
  od;
  # For the image:
  InitialDataForImageRecogNode(ri).blocks := blocks;
  AddMethod(InitialDataForImageRecogNode(ri).hints, FindHomMethodsProjective.BlocksModScalars, 2000);
  # For the kernel:
  InitialDataForKernelRecogNode(ri).blocks := blocks;
  AddMethod(InitialDataForKernelRecogNode(ri).hints, FindHomMethodsProjective.BlocksBackToMats, 2000);
  return Success;
end);

RECOG.HomBackToMats := function(el)
  # We assume that el is block diagonal with the last block being scalar.
  # This just norms this last block to 1.
  local d;
  d := Length(el);
  return (el[d,d]^-1)*el;
end;

#! @BeginChunk BlocksBackToMats
#! TODO
#! @EndChunk
BindRecogMethod(FindHomMethodsProjective, "BlocksBackToMats",
"Hint TODO",
function(ri,G)
  # This is only called as hint from Blocks, so we know that we in fact
  # have scalar blocks along the diagonal and nothing else.
  local H,hom,newgens;
  newgens := List(GeneratorsOfGroup(G),RECOG.HomBackToMats);
  H := Group(newgens);
  hom := GroupHomomorphismByFunction(G,H,RECOG.HomBackToMats);
  SetHomom(ri,hom);

  # hints for the image:
  Setmethodsforimage(ri,FindHomDbMatrix);
  InitialDataForImageRecogNode(ri).blocks := ri!.blocks{[1..Length(ri!.blocks)-1]};
  AddMethod(InitialDataForImageRecogNode(ri).hints, FindHomMethodsMatrix.BlockScalar, 2000 );

  # This is an isomorphism:
  findgensNmeth(ri).method := FindKernelDoNothing;

  return Success;
end);
