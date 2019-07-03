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

SLPforElementFuncsGeneric.TrivialGroup := function(ri,g)
  return StraightLineProgramNC( [ [1,0] ], 1 );
end;

#! @BeginChunk TrivialGroup
#! This method is successful if and only if all generators of a group
#! <A>G</A> are equal to the identity. Otherwise, it returns
#! <C>NeverApplicable</C> indicating that it will never succeed. This method
#! is only installed to handle the trivial case such that we do not have to
#! take this case into account in the other methods.
#! @EndChunk
FindHomMethodsGeneric.TrivialGroup := function(ri, G)
    local gens;
    gens := GeneratorsOfGroup(G);
    if not ForAll(gens, ri!.isone) then
        return NeverApplicable;
    fi;
    SetSize(ri, 1);
    Setslpforelement(ri, SLPforElementFuncsGeneric.TrivialGroup);
    Setslptonice(ri, StraightLineProgramNC([[[1,0]]],Length(gens)));
    SetFilterObj(ri, IsLeaf);
    return Success;
end;
