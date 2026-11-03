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
#############################################################################

# For the constructive recognition of classical groups in their natural
# representation: level 1 reports the phases, 2 each step, 3 each rejected
# random element.
DeclareInfoClass( "InfoRecog_ClassicalNatural" );

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

# Whether <base1> and <base2> span independent subspaces on whose sum
# <g1> and <g2> act irreducibly.
RECOG.CheckNewStingrayGroup := function(g1,base1,g2,base2,q)
local baseSum, module;

    baseSum := Concatenation(base1,base2);
    baseSum := TriangulizedMat(baseSum);
    if IsZero(Last(baseSum)) then
        return false;
    fi;

    g1 := TransposedMat(StripMemory(g1));
    g2 := TransposedMat(StripMemory(g2));
    module := GModuleByMats( [g1,g2], GF(q) );
    module := MTX.InducedActionSubmoduleNB( module, baseSum );
    return MTX.IsIrreducible(module);
end;

# Whether a root of the irreducible factor <irrfact>, of degree <k>, of a
# characteristic polynomial over GF(p^f) has order divisible by a
# primitive prime divisor of p^(f*k)-1.
RECOG.IsPpdStingrayElement := function( p, f, k, irrfact )
    local c, e,  R,  pm,  g, islarge, F;

    F := GF(p^f);
    c := irrfact;
    R := PolynomialRing(F);

    e  := k;
    ## find the noppds and ppds parts
    pm := PrimitivePrimeDivisors( f*e, p );
    ## pm contains two fields, noppds and ppds.
    ## ppds is the product of all ppds of p^(ae)-1
    ## and noppds is p^(ae)-1/ppds.

    ## get rid of the non-ppd part
    ## g will be x^noppds in F[x]/<c>
    g := PowerMod( Indeterminate(F), pm.noppds, c );

    ## now we know that <m> is a ppd-element

    ## if g is one there is no ppd involved
    if IsOne(g) then
        return false;
    else
        return true;
    fi;

end;
