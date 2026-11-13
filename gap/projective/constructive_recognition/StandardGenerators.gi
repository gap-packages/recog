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
##  (e_1, f_1, e_2, f_2, ..., e_m, f_m, w_1, ..., w_d0), with hyperbolic
##  pairs (e_i, f_i) and an anisotropic part <w_1, ..., w_d0> orthogonal to
##  them, of dimension d0 = 0, except for the orthogonal types "O-"
##  (d0 = 2) and "O" (odd degree, d0 = 1); "O+" has d0 = 0.
##
##  Orthogonal groups are those of odd characteristic only. Their quadratic
##  form Q is then determined by its polar form beta, Q(x) = beta(x, x)/2,
##  and the code works with beta alone; the classical group is Omega.
##
#############################################################################

# The types of orthogonal groups, by the sign of the form
RECOG.OrthogonalTypes := ["O+", "O-", "O"];

# The type of the classical groups which act on the span of the first n
# vectors of a standard basis of type <type>, n < d even: "O+" for the
# orthogonal types, which [EHNPR] calls the type of a prefix
RECOG.ClassicalPrefixType := function(type)
  if type in RECOG.OrthogonalTypes then
    return "O+";
  fi;
  return type;
end;

# The Gram matrix, relative to a standard basis, of the standard form of
# type <type> on GF(q)^<d>, q = Size(<f>): diag(J, ..., J, J0) with
# J = [[0,1],[-1,0]] for "Sp" and J = [[0,1],[1,0]] otherwise, and J0 the
# Gram matrix on the anisotropic part: [-1/2] for "O", that is,
# Q(w_1) = -1/4, and diag(-2, 2 gamma), gamma = Z(q), for "O-", that is,
# Q(w_1) = -1 and Q(w_2) = gamma. Type "SL" has no form; its standard scalar
# product has Gram matrix the identity.
RECOG.ClassicalStandardForm := function(type, d, f)
  local eps, J, m, i;

  if type = "SL" then
    return IdentityMat(d, f);
  fi;
  if not type in Concatenation(["Sp", "SU"], RECOG.OrthogonalTypes) then
    ErrorNoReturn("RECOG.ClassicalStandardForm: unsupported type ", type);
  fi;
  if type in RECOG.OrthogonalTypes and IsEvenInt(Size(f)) then
    ErrorNoReturn("RECOG.ClassicalStandardForm: orthogonal types need odd q");
  fi;
  if type = "O" and IsEvenInt(d) then
    ErrorNoReturn("RECOG.ClassicalStandardForm: <d> must be odd");
  elif type <> "O" and IsOddInt(d) then
    ErrorNoReturn("RECOG.ClassicalStandardForm: <d> must be even");
  fi;

  # beta(f_i, e_i)
  if type = "Sp" then
    eps := -One(f);
  else
    eps := One(f);
  fi;
  m := QuoInt(d, 2);
  if type = "O-" then
    m := m - 1;
  fi;
  J := NullMat(d, d, f);
  for i in [1, 3 .. 2 * m - 1] do
    J[i, i + 1] := One(f);
    J[i + 1, i] := eps;
  od;
  if type = "O" then
    J[d, d] := -One(f) / 2;
  elif type = "O-" then
    J[d - 1, d - 1] := -2 * One(f);
    J[d, d] := 2 * Z(Size(f));
  fi;
  ConvertToMatrixRep(J, f);
  return J;
end;

# Forms are records with components `gram`, `frob` and `field`, standing
# for the form beta(x, y) = x * gram * y^frob on row vectors over the
# finite field `field`, where y^frob raises each entry of y to the power
# frob: frob = 1 for a bilinear form, and frob = q0 for a sesquilinear form
# over GF(q0^2).
# All forms here are reflexive, beta(y, x) = eps * beta(x, y)^frob with
# eps = 1 or -1, as alternating, hermitian and symmetric forms are.

# The standard form of type <type>, "Sp", "SU" or an orthogonal type, on
# GF(q)^<d>, q = Size(<f>), as a form record
RECOG.ClassicalForm := function(type, d, f)
  local frob;

  frob := 1;
  if type = "SU" then
    frob := RootInt(Size(f), 2);
  fi;
  return rec( gram := RECOG.ClassicalStandardForm(type, d, f),
              frob := frob, field := f );
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
# alternating, hermitian or symmetric form in odd characteristic, where
# dual[i] = vecs[i] * form.gram. Returns a record with components `e`,
# `f`, `eJ` = e * form.gram, `fJ` and `drop`, two positions in <vecs>
# whose rows together with e and f span the span of <vecs>, or fail if
# the step finds no pair; it finds one if the span is non-degenerate of
# dimension at least 2, except for a symmetric form on an anisotropic
# span, of dimension at most 2.
RECOG.FormHyperbolicPairStep := function(form, vecs, dual)
  local conj, x, cx, a, lam, y, yJ, cy, b, c, e, eJ, j, z, zJ, s, t, k, ce,
        i, drop, bJ, f, fJ;

  if Length(vecs) < 2 then
    return fail;
  fi;
  conj := v -> RECOG.FormConjugate(form, v);

  # an isotropic vector e, and the position j of a row of <vecs> whose
  # coefficient in e is nonzero: x = vecs[1], or for y in <vecs[1], vecs[2]>
  # orthogonal to x, y or x + c y with c^(frob+1) = -beta(x, x) / beta(y, y)
  x := vecs[1];
  cx := conj(x);
  a := dual[1] * cx;
  if IsZero(a) then
    e := x;
    eJ := dual[1];
    j := 1;
  else
    lam := dual[2] * cx / a;
    y := vecs[2] - lam * x;
    yJ := dual[2] - lam * dual[1];
    cy := conj(y);
    b := yJ * cy;
    c := fail;
    if not IsZero(b) then
      c := RootFFE(form.field, -a / b, form.frob + 1);
    fi;
    if IsZero(b) then
      e := y;
      eJ := yJ;
      j := 2;
    elif c <> fail then
      e := x + c * y;
      eJ := dual[1] + c * yJ;
      j := 2;
    elif Length(vecs) < 3 then
      return fail;
    else
      # <x, y> is an anisotropic plane of a symmetric form, as the norm
      # c -> c^(frob+1) is onto for frob > 1. For z in <vecs[1], ...,
      # vecs[3]> orthogonal to x and y, the norm of z + s x + t y is
      # beta(z, z) + a s^2 + b t^2, and one of the s in GF(q) makes it 0
      # for some t ([DR], Remark 8.17)
      z := vecs[3] - (dual[3] * cx / a) * x - (dual[3] * cy / b) * y;
      zJ := dual[3] - (dual[3] * cx / a) * dual[1] - (dual[3] * cy / b) * yJ;
      c := zJ * conj(z);
      s := Zero(form.field);
      k := 0;
      repeat
        t := RootFFE(form.field, -(c + a * s^2) / b, 2);
        if t = fail then
          s := PrimitiveRoot(form.field)^k;
          k := k + 1;
        fi;
      until t <> fail;
      e := z + s * x + t * y;
      eJ := zJ + s * dual[1] + t * yJ;
      j := 3;
    fi;
  fi;
  ce := conj(e);

  # b with beta(b, e) <> 0, among the rows other than the j-th: one exists,
  # as e is isotropic and the span non-degenerate
  i := First([1 .. Length(vecs)], k -> k <> j and not IsZero(dual[k] * ce));
  if i = fail then
    return fail;
  fi;
  drop := [j, i];
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
# that is, if the Gram matrix of <vecs> has rank less than 2, or the span
# modulo its radical is anisotropic.
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

# A basis (w_1) or (w_1, w_2) of the anisotropic span of the rows <vecs>,
# of dimension 1 or 2, for the symmetric form <form>, with the values of
# the standard form on the anisotropic part (see
# RECOG.ClassicalStandardForm), where dual[i] = vecs[i] * form.gram; or
# fail if there is none. In dimension 1 that needs -2 beta(w, w) to be a
# square for w in <vecs>, which holds for one of the forms beta and
# gamma*beta; in dimension 2 any anisotropic plane has such a basis.
RECOG.FormAnisotropicBasis := function(form, vecs, dual)
  local F, x, a, y, b, s, k, t, w1, w2;

  F := form.field;
  if form.frob <> 1 or not Length(vecs) in [1, 2] then
    return fail;
  fi;
  x := vecs[1];
  a := dual[1] * x;
  if IsZero(a) then
    return fail;
  elif Length(vecs) = 1 then
    s := RootFFE(F, -1 / (2 * a), 2);
    if s = fail then
      return fail;
    fi;
    return [s * x];
  fi;

  # y orthogonal to x; w_1 = s x + t y of norm a s^2 + b t^2 = -2, which
  # one of the s in GF(q) admits, and w_2 a multiple of b t x - a s y
  y := vecs[2] - (dual[2] * x / a) * x;
  b := (dual[2] - (dual[2] * x / a) * dual[1]) * y;
  if IsZero(b) then
    return fail;
  fi;
  s := Zero(F);
  k := 0;
  repeat
    t := RootFFE(F, (-2 - a * s^2) / b, 2);
    if t = fail then
      s := PrimitiveRoot(F)^k;
      k := k + 1;
    fi;
  until t <> fail;
  w1 := s * x + t * y;
  # w_2 has norm -2 a b, and -a b is a non-square as the plane is
  # anisotropic
  w2 := RootFFE(F, -Z(Size(F)) / (a * b), 2);
  if w2 = fail then
    return fail;
  fi;
  w2 := w2 * (b * t * x - a * s * y);
  return [w1, w2];
end;

# A standard basis (e_1, f_1, e_2, f_2, ..., w_1, ..., w_d0) of the span of
# the rows <vecs> for <form>, as for RECOG.FormHyperbolicPairStep and
# RECOG.FormAnisotropicBasis, or fail if the form is degenerate on that
# span, or its anisotropic part has no basis with the standard values
RECOG.FormStandardBasis := function(form, vecs)
  local dual, res, step, aniso, ce, cf, eps, keep, bf, be, i;

  vecs := ShallowCopy(vecs);
  dual := List(vecs, v -> v * form.gram);
  res := [];
  while vecs <> [] do
    step := RECOG.FormHyperbolicPairStep(form, vecs, dual);
    if step = fail then
      aniso := RECOG.FormAnisotropicBasis(form, vecs, dual);
      if aniso = fail then
        return fail;
      fi;
      return Concatenation(res, aniso);
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

# Whether the nonzero <x> in GF(<q>), q odd, is a square
RECOG.IsSquareFFE := {x, q} -> IsOne(x^((q - 1) / 2));

# The type, an element of RECOG.OrthogonalTypes, of the restriction of the
# symmetric form <form> to the span of the rows <vecs>, which must be
# non-degenerate: of dimension n even, it is "O+" if and only if
# (-1)^(n/2) times the determinant of its Gram matrix is a square
# ([LGO09], Lemma 2.3, see [EHNPR], 'GoingDown algorithm')
RECOG.FormOrthogonalType := function(form, vecs)
  local n, det;

  n := Length(vecs);
  if IsOddInt(n) then
    return "O";
  fi;
  det := (-1)^(n / 2) * DeterminantMat(RECOG.FormGram(form, vecs));
  if RECOG.IsSquareFFE(det, Size(form.field)) then
    return "O+";
  fi;
  return "O-";
end;

# The form, as a form record, of type <type>, "Sp", "SU" or an orthogonal
# type, which the matrices <gens> over <f> preserve, and which is unique up
# to a scalar: g * gram * (g^frob)^T = gram for g in gens. For "SU" it is
# hermitian, and for "O" (odd degree) it is the multiple for which a
# standard basis exists: [EHNPR], 'Classical forms and classical groups',
# Lemma on standard bases. For even degree every multiple has one.
RECOG.ClassicalInvariantForm := function(type, gens, f)
  local M, frob, F, Fq, d, std;

  M := GModuleByMats(gens, f);
  if type = "Sp" then
    return rec( gram := MTX.InvariantBilinearForm(M), frob := 1,
                field := f );
  elif type in RECOG.OrthogonalTypes then
    F := MTX.InvariantBilinearForm(M);
    d := NrRows(F);
    std := RECOG.ClassicalStandardForm(type, d, f);
    # for d odd, det(c F) = c^d det(F) lies in the square class of c det(F)
    if IsOddInt(d) and not RECOG.IsSquareFFE(
           DeterminantMat(F) / DeterminantMat(std), Size(f)) then
      F := PrimitiveRoot(f) * F;
    fi;
    ConvertToMatrixRep(F, f);
    return rec( gram := F, frob := 1, field := f );
  fi;
  if type <> "SU" then
    ErrorNoReturn("RECOG.ClassicalInvariantForm: unsupported type ", type);
  fi;

  # (F^frob)^T = c*F with c^(frob+1) = 1, so F + (F^frob)^T is hermitian
  # unless c = -1; then alpha*F is, for alpha^frob = -alpha
  frob := RootInt(Size(f), 2);
  F := MTX.InvariantSesquilinearForm(M);
  Fq := TransposedMat(List(F, r -> List(r, x -> x^frob)));
  if IsZero(F + Fq) then
    F := PrimitiveRoot(f)^((frob + 1) / 2) * F;
  else
    F := F + Fq;
  fi;
  ConvertToMatrixRep(F, f);
  return rec( gram := F, frob := frob, field := f );
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

# The standard generators of Omega(<d>, q) of the orthogonal type <type>,
# q = Size(<f>) odd, for RECOG.ClassicalStandardGenerators, as a record
# with the components named by RECOG.ClassicalStandardGeneratorNames. With
# gamma = Z(q), m the number of hyperbolic pairs and sign = (-1)^(m+1):
#  - "O+": on (e_1, f_1, e_2, f_2), s = [[0,0,0,-1],[0,0,-1,0],[0,1,0,0],
#    [1,0,0,0]], t = [[1,0,0,-1],[0,1,0,0],[0,1,1,0],[0,0,0,1]],
#    delta = diag(gamma, gamma^-1, gamma, gamma^-1), s' = (e_1, e_2)^-
#    (f_1, f_2)^-, t' = [[1,0,1,0],[0,1,0,0],[0,0,1,0],[0,-1,0,1]] and
#    delta' = diag(gamma, gamma^-1, gamma^-1, gamma)
#  - "O-": on (e_1, f_1, w_1, w_2), s = [[0,1,0,0],[1,0,0,0],[0,0,-1,0],
#    [0,0,0,1]], t = [[1,1,1,0],[0,1,0,0],[0,2,1,0],[0,0,0,1]] and delta =
#    [[gamma,0,0,0],[0,gamma^-1,0,0],[0,0,A,B],[0,0,C,A]], where for a
#    primitive element g of GF(q^2) with g^(q+1) = gamma and
#    a = g^((q+1)/2), A = (g^(q-1) + g^(1-q))/2,
#    B = (g^(q-1) - g^(1-q))/(2a) and C = gamma B. [LGO09], Section 3,
#    has B and C interchanged, a misprint ([EHNPR], Definition of the
#    field constants)
#  - "O": on (e_1, f_1, w_1), s = [[0,1,0],[1,0,0],[0,0,-1]],
#    t = [[1,1,2],[0,1,0],[0,1,1]] and delta = diag(gamma^2, gamma^-2, 1)
#  - u ("O-", "O"): (e_1, e_2)^-(f_1, f_2)^-, the identity for m = 1
#  - v: (e_1, ..., e_m)^sign (f_1, ..., f_m)^sign
RECOG.OrthogonalStandardGenerators := function(type, d, f)
  local q, gamma, m, sign, res, g, a, A, B, idx;

  q := Size(f);
  gamma := Z(q);
  m := QuoInt(d, 2);
  if type = "O-" then
    m := m - 1;
  fi;
  sign := (-1)^(m + 1);
  res := rec( v := RECOG.SignedCycle(d, f, [1, 3 .. 2 * m - 1], sign)
                   * RECOG.SignedCycle(d, f, [2, 4 .. 2 * m], sign) );

  if type = "O+" then
    if m < 2 then
      ErrorNoReturn("RECOG.OrthogonalStandardGenerators: \"O+\" needs ",
                    "<d> >= 4");
    fi;
    res.s := RECOG.EmbedBlock(d, f, [1 .. 4],
                 [[0, 0, 0, -1], [0, 0, -1, 0], [0, 1, 0, 0], [1, 0, 0, 0]]);
    res.t := RECOG.EmbedBlock(d, f, [1 .. 4],
                 [[1, 0, 0, -1], [0, 1, 0, 0], [0, 1, 1, 0], [0, 0, 0, 1]]);
    res.delta := RECOG.EmbedBlock(d, f, [1 .. 4],
                     DiagonalMat([gamma, gamma^-1, gamma, gamma^-1]));
    res.("s'") := RECOG.SignedCycle(d, f, [1, 3], -1)
                  * RECOG.SignedCycle(d, f, [2, 4], -1);
    res.("t'") := RECOG.EmbedBlock(d, f, [1 .. 4],
                      [[1, 0, 1, 0], [0, 1, 0, 0], [0, 0, 1, 0],
                       [0, -1, 0, 1]]);
    res.("delta'") := RECOG.EmbedBlock(d, f, [1 .. 4],
                          DiagonalMat([gamma, gamma^-1, gamma^-1, gamma]));
    return res;
  fi;

  res.u := IdentityMat(d, f);
  if m >= 2 then
    res.u := RECOG.SignedCycle(d, f, [1, 3], -1)
             * RECOG.SignedCycle(d, f, [2, 4], -1);
  fi;
  if type = "O-" then
    idx := [1, 2, d - 1, d];
    g := Z(q^2);
    a := g^((q + 1) / 2);
    A := (g^(q - 1) + g^(1 - q)) / 2;
    B := (g^(q - 1) - g^(1 - q)) / (2 * a);
    res.s := RECOG.EmbedBlock(d, f, idx,
                 [[0, 1, 0, 0], [1, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 1]]);
    res.t := RECOG.EmbedBlock(d, f, idx,
                 [[1, 1, 1, 0], [0, 1, 0, 0], [0, 2, 1, 0], [0, 0, 0, 1]]);
    res.delta := RECOG.EmbedBlock(d, f, idx,
                     [[gamma, 0, 0, 0], [0, gamma^-1, 0, 0],
                      [0, 0, A, B], [0, 0, gamma * B, A]]);
  else
    idx := [1, 2, d];
    res.s := RECOG.EmbedBlock(d, f, idx, [[0, 1, 0], [1, 0, 0], [0, 0, -1]]);
    res.t := RECOG.EmbedBlock(d, f, idx, [[1, 1, 2], [0, 1, 0], [0, 1, 1]]);
    res.delta := RECOG.EmbedBlock(d, f, idx,
                     DiagonalMat([gamma^2, gamma^-2, One(f)]));
  fi;
  return res;
end;

# The standard generators of CL(<d>, q) of type <type> relative to the
# standard basis of GF(q)^<d>, q = Size(<f>), with gamma = Z(q) ([EHNPR],
# Definition of standard generators). For SL, for Sp with q odd, for SU
# with q odd and d even, and for the orthogonal types with q odd, they are
# those of Leedham-Green and O'Brien [LGO09], Section 3, Table 1, relative
# to the basis order of [EHNPR], except u for SL and y, which are the
# identity there. For SU, q = q0^2, alpha = gamma^((q0+1)/2) and
# gamma0 = gamma^(q0+1). For the orthogonal types the components are those
# of RECOG.OrthogonalStandardGenerators and `all`; otherwise
# it returns a record with the following components:
#  - `s`, `t`, `delta`: [[0,1],[-1,0]], [[1,1],[0,1]] and
#    diag(gamma, gamma^-1) on (e_1, f_1); for "SU", [[0,alpha],
#    [alpha^-q0,0]], [[1,alpha],[0,1]] and diag(gamma0, gamma0^-1)
#  - `u` (not "SL"): (e_1, e_2)(f_1, f_2), the identity for d = 2
#  - `x`: for "Sp", the matrix [[1,0,0,0],[0,1,1,0],[0,0,1,0],[1,0,0,1]]
#    on (e_1, f_1, e_2, f_2); for "SU", [[1,0,1,0],[0,1,0,0],[0,0,1,0],
#    [0,-1,0,1]]; for "SL" and d even, the signed cycle
#    (e_1, f_1, e_2, f_2)^-; the identity if it does not fit
#  - `y` (only "SU"): diag(gamma, gamma^-q0, gamma^-1, gamma^q0) on
#    (e_1, f_1, e_2, f_2), the identity for d = 2
#  - `v`: (e_1, ..., e_m)(f_1, ..., f_m); for "SL" and d odd, the map
#    v_1 -> v_d, v_i -> -v_(i-1)
#  - `all`: the list of these, in the order of
#    RECOG.ClassicalStandardGeneratorNames
RECOG.ClassicalStandardGenerators := function(type, d, f)
  local gamma, m, odd, e, q0, alpha, gamma0, res, i;

  if not type in Concatenation(["SL", "Sp", "SU"], RECOG.OrthogonalTypes)
     then
    ErrorNoReturn("RECOG.ClassicalStandardGenerators: unsupported type ",
                  type);
  fi;
  if type in ["Sp", "SU", "O+", "O-"] and IsOddInt(d) then
    ErrorNoReturn("RECOG.ClassicalStandardGenerators: <d> must be even");
  elif type = "O" and IsEvenInt(d) then
    ErrorNoReturn("RECOG.ClassicalStandardGenerators: <d> must be odd");
  elif type in RECOG.OrthogonalTypes and IsEvenInt(Size(f)) then
    ErrorNoReturn("RECOG.ClassicalStandardGenerators: orthogonal types ",
                  "need odd q");
  fi;

  gamma := Z(Size(f));
  m := QuoInt(d, 2);
  odd := [1, 3 .. 2 * m - 1];
  e := [2, 4 .. 2 * m];

  if type in RECOG.OrthogonalTypes then
    res := RECOG.OrthogonalStandardGenerators(type, d, f);
  elif type = "SU" then
    q0 := RootInt(Size(f), 2);
    alpha := gamma^((q0 + 1) / 2);
    gamma0 := gamma^(q0 + 1);
    res := rec(
      s := RECOG.EmbedBlock(d, f, [1, 2], [[0, alpha], [alpha^-q0, 0]]),
      t := RECOG.EmbedBlock(d, f, [1, 2], [[1, alpha], [0, 1]]),
      delta := RECOG.EmbedBlock(d, f, [1, 2],
                                [[gamma0, 0], [0, gamma0^-1]]),
    );
  else
    res := rec(
      s := RECOG.EmbedBlock(d, f, [1, 2], [[0, 1], [-1, 0]]),
      t := RECOG.EmbedBlock(d, f, [1, 2], [[1, 1], [0, 1]]),
      delta := RECOG.EmbedBlock(d, f, [1, 2], [[gamma, 0], [0, gamma^-1]]),
    );
  fi;

  if type in ["Sp", "SU"] then
    res.u := IdentityMat(d, f);
    res.x := IdentityMat(d, f);
    res.y := IdentityMat(d, f);
    if m >= 2 then
      res.u := RECOG.SignedCycle(d, f, [1, 3], 1)
               * RECOG.SignedCycle(d, f, [2, 4], 1);
    fi;
    if m >= 2 and type = "Sp" then
      res.x := RECOG.EmbedBlock(d, f, [1 .. 4],
                   [[1, 0, 0, 0], [0, 1, 1, 0], [0, 0, 1, 0], [1, 0, 0, 1]]);
    elif m >= 2 then
      res.x := RECOG.EmbedBlock(d, f, [1 .. 4],
                   [[1, 0, 1, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, -1, 0, 1]]);
      res.y := RECOG.EmbedBlock(d, f, [1 .. 4],
                   DiagonalMat([gamma, gamma^-q0, gamma^-1, gamma^q0]));
    fi;
    res.v := RECOG.SignedCycle(d, f, odd, 1) * RECOG.SignedCycle(d, f, e, 1);
  elif type = "SL" and IsEvenInt(d) then
    if d >= 4 then
      res.x := RECOG.SignedCycle(d, f, [1 .. 4], -1);
    else
      res.x := IdentityMat(d, f);
    fi;
    res.v := RECOG.SignedCycle(d, f, odd, 1) * RECOG.SignedCycle(d, f, e, 1);
  elif type = "SL" then
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
  elif type = "SU" then
    return ["s", "t", "delta", "u", "v", "x", "y"];
  elif type = "O+" then
    return ["s", "t", "delta", "s'", "t'", "delta'", "v"];
  elif type in ["O-", "O"] then
    return ["s", "t", "delta", "u", "v"];
  fi;
  ErrorNoReturn("RECOG.ClassicalStandardGeneratorNames: unsupported type ",
                type);
end;
