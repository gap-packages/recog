#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This file's authors include Max Neunhöffer, Ákos Seress.
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

# The monomial matrix <P> as a record for RECOG.MonomialConjugate: `pi`
# and `c` with P[i, pi[i]] = lambda c[i], and `scaled`, the i with
# c[i] <> 1. Conjugation by P does not see the scalar lambda, which makes
# most c[i] equal to 1.
RECOG.MonomialData := function(P)
  local n, pi, c, counts, lambda;

  n := NrRows(P);
  pi := List([1 .. n], i -> PositionNonZero(P[i]));
  c := List([1 .. n], i -> P[i, pi[i]]);
  counts := Collected(c);
  lambda := First(counts, x -> x[2] = Maximum(List(counts, y -> y[2])))[1];
  c := c / lambda;
  return rec( pi := pi, c := c,
              scaled := Filtered([1 .. n], i -> not IsOne(c[i])) );
end;

# P M P^-1 for the square matrix <M> and the monomial matrix P of the
# record <mon> of RECOG.MonomialData, as a new list of mutable rows: the
# entry [i, j] is c[i] M[pi[i], pi[j]] c[j]^-1. It costs O(n) per row of M
# and per entry of mon.scaled.
RECOG.MonomialConjugate := function(M, mon)
  local N, i, c, row;

  N := M{mon.pi}{mon.pi};
  for i in mon.scaled do
    MultVector(N[i], mon.c[i]);
  od;
  for i in mon.scaled do
    c := mon.c[i]^-1;
    for row in N do
      row[i] := row[i] * c;
    od;
  od;
  return N;
end;
