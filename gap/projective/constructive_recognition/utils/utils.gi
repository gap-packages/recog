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



#############################################################################
#############################################################################
######## General utils ######################################################
#############################################################################
#############################################################################



RECOG.LinearAction := function(bas,field,el)
  local mat,vecs;
  if IsGroup(el) then
      return Group(List(GeneratorsOfGroup(el),
                        x->RECOG.LinearAction(bas,field,x)));
  fi;
  if IsBasis(bas) then
      vecs := BasisVectors(bas);
  else
      vecs := bas;
      bas := Basis(VectorSpace(field,bas),bas);
  fi;
  mat := List(vecs,v->Coefficients(bas,v*el));
  ConvertToMatrixRep(mat,field);
  return mat;
end;
