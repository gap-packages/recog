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
##  Generic code for projective groups.
##
#############################################################################

# Assumes <m> is a non-empty square matrix defined over a field. <m> defines a
# projective one iff it is a non-zero scalar multiple of the identity matrix.
InstallGlobalFunction( IsOneProjective,
  function(m)
    Assert(1, NrRows(m) > 0 and NrRows(m) = NrCols(m));
    return not IsZero(m[1,1]) and RECOG.IsScalarMat(m) <> false;
  end );

# Assumes <a> and <b> are non-empty equal-dimension square matrices over equal
# fields, and that the first row of <a> contains a non-zero entry.
#
# <a> and <b> define equal projective elements, or are "equal modulo scalars",
# iff there exists a (non-zero) scalar <s> in the field such that <s * a = b>.
InstallGlobalFunction( IsEqualProjective,
  function(a, b)
    local n, p, s;
    n := NrRows(a);
    Assert(1, n > 0 and n = NrRows(b) and n = NrCols(a) and n = NrCols(b));
    p := First([1..n], i -> not IsZero(a[1,i])); # Find non-zero entry in <a[1]>
    Assert(1, p <> fail);
    s := b[1,p] / a[1,p]; # The unique scalar <s> with <s * a[1,p] = b[1,p]>.
    if IsZero(s) then
      return false; # <a[1,p] <> 0 = b[1,p]>, so <a> and <b> are not equal.
    elif IsRowListMatrix(a) and IsRowListMatrix(b) then
      # Separate case for performance reasons
      return ForAll([1 .. n], i -> s * a[i] = b[i]);
    fi;
    return s * a = b;
  end );

# The projective order of an invertible square matrix <m> over a finite field is
# the least positive integer <k> such that <m ^ k> is a projective one.
RECOG.ProjectiveOrder := m -> ProjectiveOrder(m)[1];

# Assumes <m> is a non-empty square matrix over a field.
#
# <m> is a scalar matrix iff it is a scalar multiple of the identity matrix,
# i.e. a diagonal square matrix with the same value along its main diagonal.
#
# If <m> is a scalar matrix, then this function returns the scalar that appears
# on its main diagonal. Otherwise, this function returns <false>.
RECOG.IsScalarMat := function(m)
  local x;
  Assert(1, NrRows(m) > 0 and NrRows(m) = NrCols(m));
  x := m[1,1];
  if ForAny([2..NrRows(m)], i -> m[i,i] <> x) or not IsDiagonalMat(m) then
    return false;
  fi;
  return x;
end;
