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
##  standard basis (e_1, f_1, ..., e_m, f_m), followed by the anisotropic
##  part for orthogonal groups of type - or o and for SU of odd degree: a
##  straight line program for an element, by Gaussian elimination as in
##  Costi (PhD thesis, Queen Mary, University of London, 2009). Each step
##  clears the images of e_1 and f_1 with RECOG.Form_MapToStd and
##  RECOG.Form_MapToF1FixingE1 (see GoingUp.gi), which use only root
##  elements on the first pair and one other pair or the anisotropic part,
##  whose words the root element record caches across calls. For SL see
##  SL/Rewrite.gi.
##
#############################################################################

# Root elements of Omega(<d>,q) of type <type>, an orthogonal type,
# q = Size(<f>), for RECOG.Form_Rewrite, on the standard generators <Y>
# with memory: those of RECOG.Omega_RootElements for the Omega^+(2m) on the m
# hyperbolic pairs, and for "O-" and "O" the component `aniso` (see
# GoingUp.gi). Returns a record with the root elements as component `R`,
# and `prefix`, the standard generators of that Omega^+(2m) as words in Y.
# For "O+" these are Y; for "O-" and "O", with k = (p-1)/2 for the
# characteristic p,
#   t+ = [t, t^u]^k,  t'+ = [t, t^(s u)]^k,  s+ = t+ ((t'+)^s)^-1 t+,
#   s'+ = u  and  v+ = v,
# and delta'+ = delta (delta^-1)^u, delta+ = (delta'+)^(s^u) for "O-",
# delta+ = Sff(2, -gamma) See(2, -gamma^-1) Sff(2, -gamma) (s+)^-1,
# delta'+ = (delta+)^-1 delta for "O". There conjugation by delta scales
# the parameters of Sff and M1j as delta+ and delta'+ do, so R is built
# with delta in their place and gets delta+ as its torus afterwards. The
# assertion checks these words against the matrices.
# For "O-" and q even, [t, t^u] = 1, as beta(w_1, w_1) = 0. There
# c = [t, (t^delta)^u] = Sff(2, lambda) and c' = [t, (t^delta)^(s u)] =
# M1j(2, lambda') with lambda, lambda' <> 0, since delta and s delta move
# w_1 off its orthogonal complement in <w_1, w_2>, and conjugation by
# delta^k divides the parameters by gamma^k; so t+ = c^(delta^k) and
# t'+ = c'^(delta^k') for the logarithms k, k' of lambda, lambda'.
# The Siegel transformations Fw of `aniso` are the conjugates of
# t = rho(f_1, -w_1) resp. rho(f_1, -2 w_1) by the delta^-k, whose
# parameters span the anisotropic part over GF(p), and Ew = Fw^s.
RECOG.Omega_RewriteRootElements := function(type, Y, d, f)
  local std, q, p, gamma, m, c, k, tp, tpp, sp, dp, dpp, P, R, P0, sff,
        see, pos, ts, alpha, toField, zF, zE;

  std := RECOG.ClassicalStandardGenerators(type, d, f);
  q := Size(f);
  p := Characteristic(f);
  gamma := Z(q);
  m := QuoInt(d, 2);
  if type = "O-" then
    m := m - 1;
  fi;
  if type = "O+" then
    return rec( R := RECOG.Omega_RootElements(Y, d, f), prefix := Y );
  fi;

  # Y = s, t, delta, u, v
  if IsEvenInt(q) then
    c := Comm(std.t, (std.t^std.delta)^std.u);
    tp := Comm(Y[2], (Y[2]^Y[3])^Y[4])^(Y[3]^LogFFE(c[1, 4], gamma));
    c := Comm(std.t, (std.t^std.delta)^(std.s * std.u));
    tpp := Comm(Y[2], (Y[2]^Y[3])^(Y[1] * Y[4]))
           ^(Y[3]^LogFFE(c[1, 3], gamma));
  else
    k := (p - 1) / 2;
    tp := Comm(Y[2], Y[2]^Y[4])^k;
    tpp := Comm(Y[2], Y[2]^(Y[1] * Y[4]))^k;
  fi;
  sp := tp * ((tpp^Y[1])^-1) * tp;
  if type = "O-" then
    dpp := Y[3] * (Y[3]^-1)^Y[4];
    dp := dpp^(Y[1]^Y[4]);
    P := [sp, tp, dp, Y[4], tpp, dpp, Y[5]];
    R := RECOG.Omega_RootElements(P, 2 * m, f);
  else
    P0 := [sp, tp, Y[3], Y[4], tpp, Y[3], Y[5]];
    R := RECOG.Omega_RootElements(P0, 2 * m, f);
    sff := RECOG.Form_RootElement(R, "Sff", 2, -gamma);
    see := RECOG.Form_RootElement(R, "See", 2, -gamma^-1);
    dp := sff * see * sff * sp^-1;
    dpp := dp^-1 * Y[3];
    P := [sp, tp, dp, Y[4], tpp, dpp, Y[5]];
    R.torus := dp;
  fi;
  Assert(1, ResultOfStraightLineProgram(SLPOfElms(P), std.all)
            = List(RECOG.ClassicalStandardGenerators("O+", 2 * m, f).all,
                   x -> RECOG.GoingUpEmbed(x, d, f)));

  # the anisotropic part; a vector z of it stands for z_1 + z_2 alpha in
  # GF(q^2), alpha = Z(q^2) for q even, resp. z_1 in GF(q)
  pos := [2 * m + 1 .. d];
  ts := List([0 .. Length(pos) * DegreeOverPrimeField(f) - 1],
             i -> std.t^(std.delta^-i));
  if type = "O-" and IsEvenInt(q) then
    toField := z -> z[1] + z[2] * Z(q^2);
  elif type = "O-" then
    alpha := Z(q^2)^((q + 1) / 2);
    toField := z -> z[1] + z[2] * alpha;
  else
    toField := z -> z[1];
  fi;
  zF := List(ts, x -> toField(-x[1]{pos}));
  zE := List(ts, x -> toField(-(x^std.s)[2]{pos}));
  R.Fw := List([0 .. Length(ts) - 1], i -> Y[2]^(Y[3]^-i));
  R.Ew := List(R.Fw, x -> x^Y[1]);
  R.bases.Fw := Basis(VectorSpace(GF(p), zF), zF);
  R.bases.Ew := Basis(VectorSpace(GF(p), zE), zE);
  R.powers.Fw := [];
  R.powers.Ew := [];
  R.aniso := rec( pos := pos, pairs := m,
                  gram := RECOG.ClassicalStandardForm(type, d, f){pos}{pos},
                  unit := IdentityMat(Length(pos), f)[1], toField := toField );
  if IsEvenInt(q) then
    R.aniso.quad :=
        RECOG.ClassicalStandardQuadraticForm(type, d, f){pos}{pos};
  fi;
  return rec( R := R, prefix := P );
end;

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

# The data for RECOG.Form_Rewrite in the group of type <type>, "Sp", "SU"
# or an orthogonal type, of degree <d> over <f>: root elements on
# generators with memory of a trivial group, as only the words matter, the
# pair cycle v, and the words for the residues which the torus leaves (see
# RECOG.Form_Rewrite). Since the memory of these generators grows with
# every call, callers replace the record after a while.
RECOG.Form_RewriteSetup := function(type, d, f)
  local std, Y, R, res, O, P, Pmat, alpha, Rot;

  std := RECOG.ClassicalStandardGenerators(type, d, f);
  Y := GeneratorsWithMemory(List(std.all, x -> ()));
  if type = "Sp" then
    R := RECOG.Sp_RootElements(Y, d, f);
  elif type = "SU" and IsOddInt(d) then
    R := RECOG.SU_RewriteRootElements(Y, d, f);
  elif type = "SU" then
    R := RECOG.SU_RootElements(Y, d, f);
  elif type in RECOG.OrthogonalTypes then
    O := RECOG.Omega_RewriteRootElements(type, Y, d, f);
    R := O.R;
  else
    ErrorNoReturn("RECOG.Form_RewriteSetup: unsupported type ", type);
  fi;
  # v^-T, by which RECOG.Form_Rewrite conjugates the transpose
  res := rec( R := R, vi := R.v^-1,
              vT := RECOG.MonomialData(TransposedMat(std.v^-1)),
              pairs := QuoInt(d, 2), count := 0 );
  if IsBound(R.aniso) then
    res.pairs := R.aniso.pairs;
  fi;

  # a word acting as diag(c, c^-1) on the second pair, and c; for SU of
  # odd degree y^u, which acts as diag(c, c^-q0) on it and as c^(q0-1) on
  # w_1, with c = gamma
  if type = "SU" and IsOddInt(d) then
    res.deltau := Y[7]^Y[4];
    res.deltaumat := RECOG.Form_RewriteBlock(std.y^std.u);
    res.gamma0 := Z(Size(f));
  elif type = "SU" then
    # delta^u
    res.deltau := Y[3]^Y[4];
    res.deltaumat := RECOG.Form_RewriteBlock(std.delta^std.u);
    res.gamma0 := std.delta[1, 1];
  elif type in RECOG.OrthogonalTypes then
    P := O.prefix;
    Pmat := List(RECOG.ClassicalStandardGenerators("O+", 2 * res.pairs, f).all,
                 x -> RECOG.GoingUpEmbed(x, d, f));
    if type = "O-" then
      # delta^u, which also acts on <w_1, w_2> as delta does
      res.deltau := Y[3]^Y[4];
      res.deltaumat := RECOG.Form_RewriteBlock(std.delta^std.u);
      res.gamma0 := Z(Size(f));
    else
      # delta+ (delta'+)^-1 = diag(1, 1, gamma^2, gamma^-2)
      res.deltau := P[3] * P[6]^-1;
      res.deltaumat := RECOG.Form_RewriteBlock(Pmat[3] * Pmat[6]^-1);
      res.gamma0 := Z(Size(f))^2;
    fi;
  fi;

  # for "O-", delta^2 (delta+ delta'+)^-1, which acts on <w_1, w_2> as
  # multiplication by x^2 for the generator x = g^(q-1) of SO^-(2), and
  # fixes the pairs; Omega^-(2) is generated by x^2. `value` reads the
  # element of GF(q^2) from the transpose of a matrix.
  if type = "O-" then
    if IsEvenInt(Size(f)) then
      alpha := Z(Size(f)^2);
    else
      alpha := Z(Size(f)^2)^((Size(f) + 1) / 2);
    fi;
    Rot := std.delta^2 * (Pmat[3] * Pmat[6])^-1;
    res.rot := rec( word := Y[3]^2 * (P[3] * P[6])^-1,
                    mat := RECOG.Form_RewriteBlock(Rot),
                    value := gT -> gT[d - 1, d - 1] + gT[d, d - 1] * alpha );
    res.rot.gen := res.rot.value(TransposedMat(Rot));
  fi;
  return res;
end;

# An SLP in the standard generators for the matrix <g> of the group, with
# the data <W> of RECOG.Form_RewriteSetup. Each step maps e_1 g to e_1 and
# then f_1 g to f_1, so that g fixes the first pair, and conjugates by v to
# bring the next pair to the front. A cleared pair has unit rows and
# columns, as g preserves its orthogonal complement, and no later step
# changes them: the root elements only touch the first pair, pairs on
# which e_1 g or f_1 g have nonzero coordinates, and the anisotropic
# part. The exception is the torus, which also scales the second pair
# (y of SU, delta+ of the orthogonal groups). That pair is a cleared one
# only in the last step, which therefore leaves diag(c, c^-1) on it, a
# power of W.deltau; for SU of odd degree diag(c, c^-q0) on it and
# c^(q0-1) on w_1, as det g = 1. For "O-" the anisotropic part is left with
# an element of Omega^-(2), a power of W.rot.word; for "O" g fixes w_1, as
# det g = 1.
# The root elements act on the columns of g, so the steps work on the
# transpose gT, where they are row operations of O(d) field operations
# each, and v is monomial: a step costs O(d^2).
RECOG.Form_Rewrite := function(W, g)
  local R, m, gT, L, Rt, mult, k, b;

  R := W.R;
  m := W.pairs;

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

  if IsBound(W.deltau) and not IsOne(gT[3, 3]) then
    k := LogFFE(gT[3, 3], W.gamma0);
    mult(W.deltaumat, -k);
    Rt := Rt * W.deltau^-k;
  fi;
  if IsBound(W.rot) and not IsOne(W.rot.value(gT)) then
    k := LogFFE(W.rot.value(gT), W.rot.gen);
    mult(W.rot.mat, -k);
    Rt := Rt * W.rot.word^-k;
  fi;
  Assert(1, IsOne(gT));
  return SLPOfElm(L * Rt^-1);
end;
