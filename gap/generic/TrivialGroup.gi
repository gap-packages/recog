#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This files's authors include Max Neunhöffer, Ákos Seress, Max Horn.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
#############################################################################

#! @BeginCode SLPforElementFuncsGeneric.TrivialGroup
SLPforElementFuncsGeneric.TrivialGroup := function(ri,g)
    if not ri!.isone(g) then
        return fail;
    fi;
    return StraightLineProgramNC( [ [1,0] ], 1 );
end;
#! @EndCode

#! @BeginChunk TrivialGroup
#! This method is successful if and only if all generators of a group
#! <A>G</A> are equal to the identity. Otherwise, it returns
#! <K>NeverApplicable</K> indicating that it will never succeed. This method
#! is only installed to handle the trivial case such that we do not have to
#! take this case into account in the other methods.
#! @EndChunk
#! @BeginCode FindHomMethodsGeneric.TrivialGroup
BindRecogMethod(FindHomMethodsGeneric, "TrivialGroup",
"go through generators and compare to the identity",
function(ri, G)
  local gens;
  # get the generators of the group
  gens := GeneratorsOfGroup(G);

  # check whether all generators are trivial
  # ri!.isone is explained below
  if not ForAll(gens, ri!.isone) then
    # NeverApplicable because it makes
    # no sense to call this method again
    return NeverApplicable;
  fi;

  # The group is trivial! Provide required information:

  # size of the group
  SetSize(ri, 1);

  # explained below
  Setslpforelement(ri, SLPforElementFuncsGeneric.TrivialGroup);

  # SLP from given generators to nice generators
  Setslptonice(ri, StraightLineProgramNC([[[1,0]]],
                   Length(gens)));

  # We have reached a leaf node.
  SetFilterObj(ri, IsLeaf);
  return Success;
end);
#! @EndCode
