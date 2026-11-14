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
##  Standard bases and standard generators of classical groups, as in
##  [EHNPR] (see GoingDown.gi), Section 'Standard generators and stingray
##  embeddings'. A standard basis is ordered
##  (e_1, f_1, e_2, f_2, ..., e_m, f_m), with hyperbolic pairs (e_i, f_i).
##
#############################################################################

# The Gram matrix, relative to a standard basis, of the standard form of
# type <type> on GF(q)^<d>, q = Size(<f>): diag(J, ..., J) with
# J = [[0,1],[-1,0]] for "Sp". Type "SL" has no form; its standard
# scalar product has Gram matrix the identity.
RECOG.ClassicalStandardForm := function(type, d, f)
  local J, i;

  if type = "SL" then
    return IdentityMat(d, f);
  fi;
  if type <> "Sp" then
    ErrorNoReturn("RECOG.ClassicalStandardForm: unsupported type ", type);
  fi;
  if IsOddInt(d) then
    ErrorNoReturn("RECOG.ClassicalStandardForm: <d> must be even");
  fi;

  J := NullMat(d, d, f);
  for i in [1, 3 .. d - 1] do
    J[i, i + 1] := One(f);
    J[i + 1, i] := -One(f);
  od;
  ConvertToMatrixRep(J, f);
  return J;
end;

# Forms are records with components `gram`, `frob` and `field`, standing
# for the form beta(x, y) = x * gram * y^frob on row vectors over the
# finite field `field`, where y^frob raises each entry of y to the power
# frob: frob = 1 for a bilinear form, and frob = q0 for a sesquilinear form
# over GF(q0^2).
# All forms here are reflexive, beta(y, x) = eps * beta(x, y)^frob with
# eps = 1 or -1, as alternating and hermitian forms are.

# The standard form of type <type>, "Sp", on GF(q)^<d>,
# q = Size(<f>), as a form record
RECOG.ClassicalForm := function(type, d, f)
  return rec( gram := RECOG.ClassicalStandardForm(type, d, f),
              frob := 1, field := f );
end;

# The vector or matrix <v> with its entries raised to the power form.frob,
# compressed: products of plain lists are slow
RECOG.FormConjugate := function(form, v)
  local res;

  if form.frob = 1 then
    return v;
  elif IsMatrix(v) then
    res := List(v, r -> List(r, c -> c^form.frob));
    ConvertToMatrixRep(res, form.field);
    return res;
  fi;
  res := List(v, c -> c^form.frob);
  ConvertToVectorRep(res, form.field);
  return res;
end;

RECOG.FormValue := {form, x, y} -> x * form.gram * RECOG.FormConjugate(form, y);

# The Gram matrix of the rows of <M>
RECOG.FormGram := {form, M} ->
    M * form.gram * TransposedMat(RECOG.FormConjugate(form, M));

# A hyperbolic pair [e, f], beta(e, e) = beta(f, f) = 0 and
# beta(e, f) = 1, in the span of the rows <vecs> for <form>, an
# alternating or hermitian form in odd characteristic, where
# dual[i] = vecs[i] * form.gram. Returns a record with components `e`,
# `f`, `eJ` = e * form.gram, `fJ` and `drop`, two positions in <vecs>
# whose rows together with e and f span the span of <vecs>, or fail if
# the step finds no pair; it finds one if the span is non-degenerate of
# dimension at least 2.
RECOG.FormHyperbolicPairStep := function(form, vecs, dual)
  local conj, x, cx, a, lam, y, yJ, cy, e, eJ, ce, i, drop, b, bJ, c, f, fJ;

  if Length(vecs) < 2 then
    return fail;
  fi;
  conj := v -> RECOG.FormConjugate(form, v);

  # an isotropic vector e: x = vecs[1], or for y in <vecs[1], vecs[2]>
  # orthogonal to x, y or x + c y with c^(frob+1) = -beta(x, x) / beta(y, y)
  x := vecs[1];
  cx := conj(x);
  a := dual[1] * cx;
  if IsZero(a) then
    e := x;
    eJ := dual[1];
    drop := 1;
  else
    lam := dual[2] * cx / a;
    y := vecs[2] - lam * x;
    yJ := dual[2] - lam * dual[1];
    cy := conj(y);
    if IsZero(yJ * cy) then
      e := y;
      eJ := yJ;
      drop := 2;
    else
      c := RootFFE(form.field, -a / (yJ * cy), form.frob + 1);
      e := x + c * y;
      eJ := dual[1] + c * yJ;
      drop := [1, 2];
    fi;
  fi;
  ce := conj(e);

  # b with beta(b, e) <> 0; for e = x + c y, b = x does
  if IsInt(drop) then
    i := PositionProperty(dual, w -> not IsZero(w * ce));
    if i = fail then
      return fail;
    fi;
    drop := [drop, i];
  else
    i := 1;
  fi;
  b := vecs[i];
  bJ := dual[i];

  # beta(e, c b) = c^frob beta(e, b), and f + c e with beta(e, f) = 1 has
  # norm beta(f, f) + c + eps c^frob, which is 0 for c = -beta(f, f) / 2
  c := (1 / (eJ * conj(b)))^form.frob;
  f := c * b;
  fJ := c * bJ;
  c := -(fJ * conj(f)) / 2;
  f := f + c * e;
  fJ := fJ + c * eJ;
  return rec( e := e, f := f, eJ := eJ, fJ := fJ, drop := drop );
end;

# A hyperbolic pair [e, f] in the span of the rows <vecs> for <form>, as
# for RECOG.FormHyperbolicPairStep. Returns fail if the span contains none,
# that is, if the Gram matrix of <vecs> has rank less than 2.
RECOG.FormHyperbolicPair := function(form, vecs)
  local G, heads, step;

  # rows of vecs whose rows in G are a basis of the row space of G span a
  # complement of the radical, which is non-degenerate
  G := RECOG.FormGram(form, vecs);
  heads := SemiEchelonMat(TransposedMat(G)).heads;
  vecs := vecs{Filtered([1 .. Length(vecs)], i -> heads[i] <> 0)};
  step := RECOG.FormHyperbolicPairStep(form, vecs,
                                       List(vecs, v -> v * form.gram));
  if step = fail then
    return fail;
  fi;
  return [step.e, step.f];
end;

# A standard basis (e_1, f_1, e_2, f_2, ...) of the span of the rows
# <vecs> for <form>, as for RECOG.FormHyperbolicPairStep, or fail if the
# form is degenerate on that span or its dimension is odd
RECOG.FormStandardBasis := function(form, vecs)
  local dual, res, step, ce, cf, eps, keep, bf, be, i;

  vecs := ShallowCopy(vecs);
  dual := List(vecs, v -> v * form.gram);
  res := [];
  while vecs <> [] do
    step := RECOG.FormHyperbolicPairStep(form, vecs, dual);
    if step = fail then
      return fail;
    fi;
    Append(res, [step.e, step.f]);

    # project the other rows onto the orthogonal complement of <e, f>:
    # x - beta(x, f) e - eps beta(x, e) f, eps = beta(f, e)
    ce := RECOG.FormConjugate(form, step.e);
    cf := RECOG.FormConjugate(form, step.f);
    eps := step.fJ * ce;
    keep := Difference([1 .. Length(vecs)], step.drop);
    vecs := vecs{keep};
    dual := dual{keep};
    for i in [1 .. Length(vecs)] do
      bf := dual[i] * cf;
      be := eps * (dual[i] * ce);
      vecs[i] := vecs[i] - bf * step.e - be * step.f;
      dual[i] := dual[i] - bf * step.eJ - be * step.fJ;
    od;
  od;
  return res;
end;

# The form, as a form record, of type <type>, "Sp", which the
# matrices <gens> over <f> preserve, and which is unique up to a scalar:
# g * gram * (g^frob)^T = gram for g in gens.
RECOG.ClassicalInvariantForm := function(type, gens, f)
  local M;

  M := GModuleByMats(gens, f);
  if type = "Sp" then
    return rec( gram := MTX.InvariantBilinearForm(M), frob := 1,
                field := f );
  fi;
  ErrorNoReturn("RECOG.ClassicalInvariantForm: unsupported type ", type);
end;

# The matrix which acts as <M> on the basis vectors with indices <idx> and
# fixes the other basis vectors of GF(q)^<d>
RECOG.EmbedBlock := function(d, f, idx, M)
  local g;
  g := IdentityMat(d, f);
  g{idx}{idx} := M * One(f);
  return g;
end;

# The signed cycle (x_1, ..., x_k)^sign on the basis vectors with indices
# <idx>: x_i -> x_(i+1) for i < k and x_k -> <sign> * x_1
RECOG.SignedCycle := function(d, f, idx, sign)
  local g, k, i;
  k := Length(idx);
  g := IdentityMat(d, f);
  for i in idx do
    g[i] := ZeroMutable(g[i]);
  od;
  for i in [1 .. k - 1] do
    g[idx[i], idx[i + 1]] := One(f);
  od;
  g[idx[k], idx[1]] := sign * One(f);
  ConvertToMatrixRep(g, f);
  return g;
end;

# The standard generators of CL(<d>, q) of type <type> relative to the
# standard basis of GF(q)^<d>, q = Size(<f>), with gamma = Z(q) ([EHNPR],
# Definition of standard generators). For SL, and for Sp with q odd, they
# are those of Leedham-Green and O'Brien, J. Algebra 322 (2009), Section 3,
# Table 1, except u for SL and y, which are the identity there.
# Returns a record with the following components:
#  - `s`, `t`, `delta`: [[0,1],[-1,0]], [[1,1],[0,1]] and
#    diag(gamma, gamma^-1) on (e_1, f_1)
#  - `u` (not "SL"): (e_1, e_2)(f_1, f_2), the identity for d = 2
#  - `x`: for "Sp", the matrix [[1,0,0,0],[0,1,1,0],[0,0,1,0],[1,0,0,1]]
#    on (e_1, f_1, e_2, f_2); for "SL" and d even, the signed cycle
#    (e_1, f_1, e_2, f_2)^-; the identity if it does not fit
#  - `v`: (e_1, ..., e_m)(f_1, ..., f_m); for "SL" and d odd, the map
#    v_1 -> v_d, v_i -> -v_(i-1)
#  - `all`: the list of these, in the order of
#    RECOG.ClassicalStandardGeneratorNames
RECOG.ClassicalStandardGenerators := function(type, d, f)
  local gamma, m, odd, e, res, i;

  if not type in ["SL", "Sp"] then
    ErrorNoReturn("RECOG.ClassicalStandardGenerators: unsupported type ",
                  type);
  fi;
  if type = "Sp" and IsOddInt(d) then
    ErrorNoReturn("RECOG.ClassicalStandardGenerators: <d> must be even");
  fi;

  gamma := Z(Size(f));
  m := QuoInt(d, 2);
  odd := [1, 3 .. 2 * m - 1];
  e := [2, 4 .. 2 * m];

  res := rec(
    s := RECOG.EmbedBlock(d, f, [1, 2], [[0, 1], [-1, 0]]),
    t := RECOG.EmbedBlock(d, f, [1, 2], [[1, 1], [0, 1]]),
    delta := RECOG.EmbedBlock(d, f, [1, 2], [[gamma, 0], [0, gamma^-1]]),
  );

  if type = "Sp" then
    res.u := IdentityMat(d, f);
    res.x := IdentityMat(d, f);
    if m >= 2 then
      res.u := RECOG.SignedCycle(d, f, [1, 3], 1)
               * RECOG.SignedCycle(d, f, [2, 4], 1);
      res.x := RECOG.EmbedBlock(d, f, [1 .. 4],
                   [[1, 0, 0, 0], [0, 1, 1, 0], [0, 0, 1, 0], [1, 0, 0, 1]]);
    fi;
    res.v := RECOG.SignedCycle(d, f, odd, 1) * RECOG.SignedCycle(d, f, e, 1);
  elif IsEvenInt(d) then
    if d >= 4 then
      res.x := RECOG.SignedCycle(d, f, [1 .. 4], -1);
    else
      res.x := IdentityMat(d, f);
    fi;
    res.v := RECOG.SignedCycle(d, f, odd, 1) * RECOG.SignedCycle(d, f, e, 1);
  else
    # v_1 -> v_d and v_i -> -v_(i-1) for i >= 2
    res.v := NullMat(d, d, f);
    res.v[1, d] := One(f);
    for i in [2 .. d] do
      res.v[i, i - 1] := -One(f);
    od;
    res.x := IdentityMat(d, f);
  fi;

  res.all := List(RECOG.ClassicalStandardGeneratorNames(type), x -> res.(x));
  for i in [1 .. Length(res.all)] do
    ConvertToMatrixRep(res.all[i], f);
  od;
  return res;
end;

# The names of the standard generators of type <type>, in the order of
# the component `all` of RECOG.ClassicalStandardGenerators
RECOG.ClassicalStandardGeneratorNames := function(type)
  if type = "SL" then
    return ["s", "t", "delta", "v", "x"];
  elif type = "Sp" then
    return ["s", "t", "delta", "u", "x", "v"];
  fi;
  ErrorNoReturn("RECOG.ClassicalStandardGeneratorNames: unsupported type ",
                type);
end;
