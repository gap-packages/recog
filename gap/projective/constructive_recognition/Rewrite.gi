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

# The data for RECOG.Form_Rewrite in the group of type <type>, "Sp", of
# degree <d> over <f>: root elements on generators with memory of a
# trivial group, as only the words matter, and the pair cycle v. Since the
# memory of these generators grows with every call, callers replace the
# record after a while.
RECOG.Form_RewriteSetup := function(type, d, f)
  local std, Y, R;

  if type <> "Sp" then
    ErrorNoReturn("RECOG.Form_RewriteSetup: unsupported type ", type);
  fi;
  std := RECOG.ClassicalStandardGenerators(type, d, f);
  Y := GeneratorsWithMemory(List(std.all, x -> ()));
  R := RECOG.Sp_RootElements(Y, d, f);
  # v^-T, by which RECOG.Form_Rewrite conjugates the transpose
  return rec( R := R, vi := R.v^-1,
              vT := RECOG.MonomialData(TransposedMat(std.v^-1)),
              count := 0 );
end;

# An SLP in the standard generators for the matrix <g> of the group, with
# the data <W> of RECOG.Form_RewriteSetup. Each step maps e_1 g to e_1 and
# then f_1 g to f_1, so that g fixes the first pair, and conjugates by v to
# bring the next pair to the front. A cleared pair has unit rows and
# columns, as g preserves its orthogonal complement, and no later step
# changes them: the root elements only touch the first pair and pairs on
# which e_1 g or f_1 g have nonzero coordinates.
# The root elements act on the columns of g, so the steps work on the
# transpose gT, where they are row operations of O(d) field operations
# each, and v is monomial: a step costs O(d^2).
RECOG.Form_Rewrite := function(W, g)
  local R, m, gT, L, Rt, k, b;

  R := W.R;
  m := NrRows(g) / 2;

  # g = L^-1 g0 Rt for the input g0
  gT := TransposedMatMutable(g);
  L := R.one;
  Rt := R.one;
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

  Assert(1, IsOne(gT));
  return SLPOfElm(L * Rt^-1);
end;
