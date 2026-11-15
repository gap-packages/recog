#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This files's authors include Max Horn.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
##
##  Constructive membership in classical groups with a form, relative to
##  the standard generators of RECOG.ClassicalStandardGenerators and the
##  standard basis (e_1, f_1, ..., e_m, f_m): a straight line program for an
##  element, by Gaussian elimination as in Costi (PhD thesis, Queen Mary,
##  University of London, 2009). Each step clears the images of e_1 and
##  f_1 with RECOG.Form_MapToStd and RECOG.Form_MapToF1FixingE1 (see
##  GoingUp.gi), which use only root elements on the first pair and one
##  other pair, whose words the root element record caches across calls.
##  For SL see SL/Rewrite.gi.
##
#############################################################################

# The matrix <A> as a record for RECOG.Form_Rewrite: `pos`, the indices
# of the rows and columns on which A differs from the identity, and
# `block`, A{pos}{pos}
RECOG.Form_RewriteBlock := function(A)
  local D, pos, i;

  D := A - One(A);
  pos := [];
  for i in [1 .. NrRows(D)] do
    if not IsZero(D[i]) then
      pos := Union(pos, [i], PositionsProperty(D[i], x -> not IsZero(x)));
    fi;
  od;
  return rec( pos := pos, block := A{pos}{pos} );
end;

# The data for RECOG.Form_Rewrite in the group of type <type>, "Sp" or
# "SU", of degree <d> over <f>: root elements on generators with memory of
# a trivial group, as only the words matter, and the pair cycle v. Since
# the memory of these generators grows with every call, callers replace
# the record after a while.
RECOG.Form_RewriteSetup := function(type, d, f)
  local std, Y, R, res;

  std := RECOG.ClassicalStandardGenerators(type, d, f);
  Y := GeneratorsWithMemory(List(std.all, x -> ()));
  if type = "Sp" then
    R := RECOG.Sp_RootElements(Y, d, f);
  elif type = "SU" then
    R := RECOG.SU_RootElements(Y, d, f);
  else
    ErrorNoReturn("RECOG.Form_RewriteSetup: unsupported type ", type);
  fi;
  # v^-T, by which RECOG.Form_Rewrite conjugates the transpose
  res := rec( R := R, vi := R.v^-1,
              vT := RECOG.MonomialData(TransposedMat(std.v^-1)),
              count := 0 );
  if type = "SU" then
    # delta^u = diag(gamma0, gamma0^-1) on the second pair
    res.deltau := Y[3]^Y[4];
    res.deltaumat := RECOG.Form_RewriteBlock(std.delta^std.u);
    res.gamma0 := std.delta[1, 1];
  fi;
  return res;
end;

# An SLP in the standard generators for the matrix <g> of the group, with
# the data <W> of RECOG.Form_RewriteSetup. Each step maps e_1 g to e_1 and
# then f_1 g to f_1, so that g fixes the first pair, and conjugates by v to
# bring the next pair to the front. A cleared pair has unit rows and
# columns, as g preserves its orthogonal complement, and no later step
# changes them: the root elements only touch the first pair and pairs on
# which e_1 g or f_1 g have nonzero coordinates. The exception is the
# torus element y of SU, which also scales the second pair. That pair is
# a cleared one only in the last step, which therefore leaves
# diag(c, c^-1) on it, c in GF(q0): a power of delta^u.
# The root elements act on the columns of g, so the steps work on the
# transpose gT, where they are row operations of O(d) field operations
# each, and v is monomial: a step costs O(d^2).
RECOG.Form_Rewrite := function(W, g)
  local R, m, gT, L, Rt, mult, k, b;

  R := W.R;
  m := NrRows(g) / 2;

  # g = L^-1 g0 Rt for the input g0
  gT := TransposedMatMutable(g);
  L := R.one;
  Rt := R.one;
  # g := g A^k for the record A of RECOG.Form_RewriteBlock
  mult := function(A, k)
    gT{A.pos} := TransposedMat(A.block^k) * gT{A.pos};
  end;

  for k in [1 .. m] do
    b := RECOG.Form_MapToStd(R, List(gT, r -> r[1]), gT);
    Rt := Rt * b.word;
    b := RECOG.Form_MapToF1FixingE1(R, List(gT, r -> r[2]), gT);
    Rt := Rt * b.word;
    if k < m then
      # g := v g v^-1
      gT := RECOG.MonomialConjugate(gT, W.vT);
      L := L * W.vi;
      Rt := Rt * W.vi;
    fi;
  od;

  if IsBound(W.deltau) and not IsOne(gT) then
    k := LogFFE(gT[3, 3], W.gamma0);
    mult(W.deltaumat, -k);
    Rt := Rt * W.deltau^-k;
  fi;
  Assert(1, IsOne(gT));
  return SLPOfElm(L * Rt^-1);
end;
