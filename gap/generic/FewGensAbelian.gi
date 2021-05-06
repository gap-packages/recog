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

#! @BeginChunk FewGensAbelian
#! If there are not too may generators (right now that means at most 200),
#! check whether they commute; if yes, dispatch to
#! <Ref Subsect="KnownNilpotent" Style="Text"/>,
#! otherwise return <K>NeverApplicable</K>.
#! @EndChunk
BindRecogMethod(FindHomMethodsGeneric, "FewGensAbelian",
"if very few generators, check IsAbelian and if yes, do KnownNilpotent",
function(ri, G)
  # If the number of generators is less than or equal to 200, then check
  # abelian and if so, hint to KnownNilpotent to write it as a direct
  # product of Sylow subgroups
  local gens, i, j, l;
  gens := GeneratorsOfGroup(G);
  l := Length(gens);
  if l > 200 then
      return NeverApplicable;
  fi;
  for i in [1..l-1] do
      for j in [i+1..l] do
          if not ri!.isequal(gens[i] * gens[j], gens[j] * gens[i]) then
              return NeverApplicable;
          fi;
      od;
  od;
  # We call KnownNilpotent:
  return FindHomMethodsGeneric.KnownNilpotent(ri, G);
end);
