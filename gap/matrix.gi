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
##  A collection of find homomorphism methods for matrix groups.
##
#############################################################################

# helper for recognition nodes for a matrix group: return the corresponding
# meataxe G-module, either a previously computed one, or a fresh copy.
#
# We do not use an attribute due to questions about the mutability status of
# recog nodes, see <https://github.com/gap-packages/recog/issues/356>.
RECOG.MeataxeModule := function(ri)
  if not IsBound(ri!.meataxemodule) then
      ri!.meataxemodule := GModuleByMats(GeneratorsOfGroup(Grp(ri)), ri!.field);
  fi;
  return ri!.meataxemodule;
end;

# helper for recognition nodes for a matrix group: test if the group
# acts irreducibly.
#
# We do not use a property due to questions about the mutability status of
# recog nodes, see <https://github.com/gap-packages/recog/issues/356>.
RECOG.IsIrreducible := function(ri)
  if not IsBound(ri!.isirreducible) then
      ri!.isirreducible := MTX.IsIrreducible(RECOG.MeataxeModule(ri));
  fi;
  return ri!.isirreducible;
end;

RECOG.SetIsIrreducible := function(ri, flag)
  Assert(0, flag = true or flag = false);
  if IsBound(ri!.isirreducible) and ri!.isirreducible <> flag then
    Error("must not change ri!.isirreducible from ", ri!.isirreducible, " to ", flag);
  fi;
  ri!.isirreducible := flag;
end;

# helper for recognition nodes for a matrix group: test if the group
# acts absolutely irreducibly.
#
# We do not use a property due to questions about the mutability status of
# recog nodes, see <https://github.com/gap-packages/recog/issues/356>.
RECOG.IsAbsolutelyIrreducible := function(ri)
  if not IsBound(ri!.isabsolutelyirred) then
      ri!.isabsolutelyirred := MTX.IsAbsolutelyIrreducible(RECOG.MeataxeModule(ri));
  fi;
  return ri!.isabsolutelyirred;
end;

RECOG.SetIsAbsolutelyIrreducible := function(ri, flag)
  Assert(0, flag = true or flag = false);
  if IsBound(ri!.isabsolutelyirred) and ri!.isabsolutelyirred <> flag then
    Error("must not change ri!.isabsolutelyirred from ", ri!.isabsolutelyirred, " to ", flag);
  fi;
  ri!.isabsolutelyirred := flag;
  if flag = true then  # absolutely irreducible implies irreducible
    RECOG.SetIsIrreducible(ri, flag);
  fi;
end;

#! @BeginChunk GoProjective
#! This method defines a homomorphism from a matrix group <A>G</A>
#! into the projective group <A>G</A> modulo scalar matrices. In fact, since
#! projective groups in &GAP; are represented as matrix groups, the
#! homomorphism is the identity mapping and the only difference is that in
#! the image the projective group methods can be applied.
#! The bulk of the work in matrix recognition is done in the projective group
#! setting.
#! @EndChunk
BindRecogMethod(FindHomMethodsMatrix, "GoProjective",
"divide out scalars and recognise projectively",
function(ri,G)
  local hom,q;
  Info(InfoRecog,2,"Going projective...");
  hom := IdentityMapping(G);
  SetHomom(ri,hom);
  # Now give hints downward:
  Setmethodsforimage(ri,FindHomDbProjective);
  # Make sure that immediate verification is performed to safeguard against the
  # kernel being too small.
  Setimmediateverification(ri, true);
  # note that RecogniseGeneric detects the use of FindHomDbProjective and
  # sets ri!.projective := true for the image
  # the kernel:
  q := Size(ri!.field);
  findgensNmeth(ri).method := FindKernelRandom;
  findgensNmeth(ri).args := [Length(Factors(q-1))+5];
  return Success;
end);

#! @BeginChunk KnownStabilizerChain
#! If a stabilizer chain is already known, then the kernel node is given
#! knowledge about this known stabilizer chain, and the image node is told to
#! use homomorphism methods from the database for permutation groups.
#! If a stabilizer chain of a parent node is already known this is used for
#! the computation of a stabilizer chain of this node. This stabilizer chain
#! is then used in the same way as above.
#! @EndChunk
BindRecogMethod(FindHomMethodsMatrix, "KnownStabilizerChain",
"use an already known stabilizer chain for this group",
function(ri,G)
  local S,hom;
  if HasStoredStabilizerChain(G) then
      Info(InfoRecog,2,"Already know stabilizer chain, using 1st orbit.");
      S := StoredStabilizerChain(G);
      hom := OrbActionHomomorphism(G,S!.orb);
      SetHomom(ri,hom);
      Setmethodsforimage(ri,FindHomDbPerm);
      InitialDataForKernelRecogNode(ri).StabilizerChainFromAbove := S;
      return Success;
  elif IsBound(ri!.StabilizerChainFromAbove) then
      Info(InfoRecog,2,"Know stabilizer chain for super group, using base.");
      S := StabilizerChain(G,rec( Base := ri!.StabilizerChainFromAbove ));
      Info(InfoRecog,2,"Computed stabilizer chain, size=",Size(S));
      hom := OrbActionHomomorphism(G,S!.orb);
      SetHomom(ri,hom);
      Setmethodsforimage(ri,FindHomDbPerm);
      InitialDataForKernelRecogNode(ri).StabilizerChainFromAbove := S;
      return Success;
  fi;
  return NeverApplicable;
end);

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
#  until not IsZero(w);
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
#  Setmethodsforimage(ri,FindHomDbPerm);
#  return true;
#end;
#
#FindHomMethodsMatrix.IsomorphismPermGroup := function(ri,G)
#  SetHomom(ri,IsomorphismPermGroup(G));
#  findgensNmeth(ri).method := FindKernelDoNothing;
#  Setmethodsforimage(ri,FindHomDbPerm);
#  return true;
#end;

#! @BeginCode AddMethod_Matrix_FindHomMethodsGeneric.TrivialGroup
AddMethod(FindHomDbMatrix, FindHomMethodsGeneric.TrivialGroup, 3100);
#! @EndCode

AddMethod(FindHomDbMatrix, FindHomMethodsMatrix.DiagonalMatrices, 1100);

AddMethod(FindHomDbMatrix, FindHomMethodsMatrix.KnownStabilizerChain, 1175);

AddMethod(FindHomDbMatrix, FindHomMethodsGeneric.FewGensAbelian, 1050);

AddMethod(FindHomDbMatrix, FindHomMethodsMatrix.ReducibleIso, 1000);

AddMethod(FindHomDbMatrix, FindHomMethodsMatrix.GoProjective, 900);



###AddMethod( FindHomDbMatrix, FindHomMethodsMatrix.SmallVectorSpace,
###           700, "SmallVectorSpace",
###           "for small vector spaces directly compute an orbit" );
