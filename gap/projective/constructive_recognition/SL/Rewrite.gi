#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This file's authors include Max Horn.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
##
##  Constructive membership in SL(d,q), relative to the standard generators
##  of RECOG.ClassicalStandardGenerators: a straight line program for an
##  element, by Gaussian elimination as in Costi (PhD thesis, Queen Mary,
##  University of London, 2009). Only the elementary matrices E(1, j, .)
##  and E(j, 1, .) of RECOG.SL_RootElements are used, whose words are cached
##  across calls, so each index costs at most 2d of them plus a
##  conjugation, and O(d^2) field operations.
##
#############################################################################

# The data for RECOG.SL_Rewrite in SL(<d>,q), q = Size(<f>), d >= 2:
# root elements on generators with memory of a trivial group, as only the
# words matter, cyc = v (d odd) or v x (d even), which permutes the
# lines <v_1>, ..., <v_d> in one cycle, and next, the index cyc maps to 1.
# For d = 2 there is one step and no conjugation, so no cyc. Since the
# memory of these generators grows with every call, callers replace the
# record after a while.
RECOG.SL_RewriteSetup := function(d, f)
  local Y, std, res;

  Y := GeneratorsWithMemory(ListWithIdenticalEntries(5, ()));
  std := RECOG.ClassicalStandardGenerators("SL", d, f);
  res := rec( R := RECOG.SL_RootElements(Y, d, f), count := 0 );
  if d = 2 then
    res.next := 2;
    return res;
  fi;
  if IsOddInt(d) then
    res.cyc := Y[4];
    res.cycmat := std.v;
  else
    res.cyc := Y[4] * Y[5];
    res.cycmat := std.v * std.x;
  fi;
  res.cyci := res.cyc^-1;
  res.cycmon := RECOG.MonomialData(res.cycmat);
  res.next := PositionNonZero(res.cycmat[1]);
  return res;
end;

# An SLP in the standard generators of SL(d,q) for the matrix <g> in
# SL(d,q), with the data <W> of RECOG.SL_RewriteSetup. Each step clears row
# 1 of g by column operations and column 1 by row operations, then
# conjugates by cyc to bring the next index to position 1. A cleared index
# has a unit row and column, which no later step changes: they only touch
# indices with nonzero entries in row or column 1, and next, the index
# cyc moves to position 1, which is not cleared before the last step.
RECOG.SL_Rewrite := function(W, g)
  local R, n, f, next, L, Rt, colOp, rowOp, k, c, j, r, i;

  R := W.R;
  n := NrRows(g);
  f := R.f;
  g := MutableCopyMat(g);
  next := W.next;

  # g = L^-1 g0 Rt for the input g0
  L := RECOG.SL_Product(R, n);
  Rt := RECOG.SL_Product(R, n);
  # g := g E(i, j, lambda) adds lambda times column i to column j
  colOp := function(i, j, lambda)
    local r;
    Rt.apply(i, j, lambda);
    for r in [1 .. n] do
      g[r, j] := g[r, j] + lambda * g[r, i];
    od;
  end;
  # g := E(i, j, lambda) g adds lambda times row j to row i; the inverse
  # E(i, j, -lambda) costs no inversion
  rowOp := function(i, j, lambda)
    L.apply(i, j, -lambda);
    AddRowVector(g[i], g[j], lambda);
  end;

  for k in [1 .. n - 1] do
    # make g[1, 1] = 1, using a second index with a nonzero entry in row
    # 1, or next
    if IsZero(g[1, 1]) then
      colOp(PositionNonZero(g[1]), 1, One(f));
    fi;
    if not IsOne(g[1, 1]) then
      j := PositionNonZero(g[1], 1);
      if j > n then
        j := next;
        colOp(1, j, One(f));
      fi;
      colOp(j, 1, (1 - g[1, 1]) / g[1, j]);
    fi;

    # the E(1, j, c[j]) add multiples of column 1 to the others, which
    # together add g[r, 1] c to each row r
    c := AdditiveInverseMutable(g[1]);
    c[1] := Zero(f);
    for j in [2 .. n] do
      Rt.apply(1, j, c[j]);
    od;
    for r in [1 .. n] do
      if not IsZero(g[r, 1]) then
        AddRowVector(g[r], c, g[r, 1]);
      fi;
    od;
    for i in [2 .. n] do
      if not IsZero(g[i, 1]) then
        rowOp(i, 1, -g[i, 1]);
      fi;
    od;

    # the one index left after the last step has the entry det g = 1
    if k < n - 1 then
      g := RECOG.MonomialConjugate(g, W.cycmon);
      L.mulPlain(W.cyci);
      Rt.mulPlain(W.cyci);
    fi;
  od;

  Assert(1, IsOne(g));
  return SLPOfElm(L.word() * Rt.word()^-1);
end;
