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
##  The parts of the GoingUp of [EHNPR] (see ../GoingUp.gi), Section
##  'GoingUp algorithm', specific to orthogonal groups.
##
##  The groups CL(U) of the steps are Omega^+(n,q), n = 2m with m odd; the
##  type of V only enters the last step. Omega contains no transvections.
##  Its root elements are the Siegel transformations
##     rho(x, y): z -> z + beta(z, y) x - beta(z, x) y - Q(y) beta(z, x) x
##  for singular x and y orthogonal to x ([EHNPR], Definition of Siegel
##  transformations), with rho(x, y) rho(x, y') = rho(x, y + y'),
##  rho(x, y)^h = rho(xh, yh) for isometries h, and rho(x, y) = rho(y, -x)
##  for singular y. The root elements See, Sff, M1j and Mj1 of ../GoingUp.gi
##  with eps = 1 and sigma the identity are Siegel transformations:
##  See(j, lambda) = rho(e_1, -lambda e_j), Sff(j, lambda) =
##  rho(f_1, -lambda f_j), M1j(j, lambda) = rho(f_1, -lambda e_j) and
##  Mj1(j, lambda) = rho(e_1, lambda f_j).
##
#############################################################################

# Root elements of Omega^+(<n>,q), q = Size(<f>), n >= 4, as words in
# the standard generators, in the record described in ../GoingUp.gi; <Y>
# are as for RECOG.Sp_RootElements. There are no components `Lf`, `Le`,
# `longUnit` and `tau`, and `s'` is the standard generator of that name.
# With gamma = Z(q): t = Sff(2, -1) and t' = M1j(2, 1), and conjugation by
# delta^-k resp. delta'^-k multiplies their parameters by gamma^(2k); the
# gamma^(2k), 0 <= k < [GF(q):GF(p)], are a basis of GF(q) over GF(p).
# Conjugation by s maps Sff(2, lambda) to See(2, lambda), and conjugation
# by s' maps M1j(2, lambda) to Mj1(2, -lambda). The element v s'^-1 fixes
# the first pair and maps the j-th to the (j+1)-th for 2 <= j < m.
RECOG.O_RootElements := function(Y, n, f)
  local s, t, delta, sp, tp, deltap, v, ext, gamma, long, sff, m1j, res, j;

  s := Y[1];
  t := Y[2];
  delta := Y[3];
  sp := Y[4];
  tp := Y[5];
  deltap := Y[6];
  v := Y[7];
  ext := DegreeOverPrimeField(f);
  gamma := Z(Size(f));
  long := List([0 .. ext - 1], k -> gamma^(2 * k));
  sff := List([0 .. ext - 1], k -> t^(delta^-k));
  m1j := List([0 .. ext - 1], k -> tp^(deltap^-k));

  res := rec(
    f := f,
    Y := Y,
    one := s^0,
    s := s,
    t := t,
    ("s'") := sp,
    v := v,
    eps := One(f),
    conj := c -> c,
    torus := delta,
    torusDiag := [gamma, gamma^-1, gamma, gamma^-1],
    gamma := gamma,
    Sff := sff,
    See := List(sff, w -> w^s),
    M1j := m1j,
    Mj1 := List(m1j, w -> w^sp),
    bases := rec( Sff := Basis(f, -long), See := Basis(f, -long),
                  M1j := Basis(f, long), Mj1 := Basis(f, -long) ),
    conjugator := [],
    powers := rec( See := [], Sff := [], M1j := [], Mj1 := [] ),
  );

  res.conjugator[2] := res.one;
  for j in [3 .. n / 2] do
    res.conjugator[j] := res.conjugator[j - 1] * v * sp^-1;
  od;
  return res;
end;

# The seed t of the GoingUp step for Omega^+(n,q), q a power of <p>
# ([EHNPR], Step 1 (Constructing the seed element)): a word in the
# components s, s', v of <Y>, which may be words or matrices, whose fixed
# space has dimension 2, and is a hyperbolic plane for m = n/2 odd. For m
# odd the pair cycle v is the product of the unsigned cycles on the e_i
# and on the f_i, and fixes <e_1 + ... + e_m, f_1 + ... + f_m>, where beta
# is m; if p divides m, then v s' is -1 on the first pair and fixes
# <e_2 + ... + e_m, f_2 + ... + f_m> instead. For m even, s v has a fixed
# space of dimension 2, which is degenerate.
RECOG.O_GoingUpSeed := function(Y, n, p)
  local m;

  m := n / 2;
  if IsEvenInt(m) then
    return Y.s * Y.v;
  elif m mod p <> 0 then
    return Y.v;
  fi;
  return Y.v * Y.("s'");
end;

# The words x of RECOG.O_GoingUpCycleBasis in the standard generators Y of
# Omega^+(n,q), as functions of Y (words or matrices) which fix the first
# r pairs pointwise: for r = 0, x = z and x = (Y[k]^(z^shift))^e z with
# z = v_U and Y[k] = t (k = 2) or t' (k = 5); for r = 1 the same with
# z = v_U s'^-1, which fixes the first pair, and Y[k]^v_U; for r = 2,
# x = y z with z = v_U s'^-1 (s'^v_U)^-1 and y one of 1, y_1^i, y_2^i,
# (y_1 y_2)^i, y_3 y_1^(i-1), i = 1, 2, for y_1, y_2, y_3 the conjugates
# of t, t', s by v_U^2. These are the first nine of the proposal (see
# RECOG.O_GoingUpCycleBasis), without repetitions from y_k^3 = 1.
RECOG.O_GoingUpCycleWords := function(n, r)
  local res, seen, shift, pos, k, e;

  if r = 2 then
    return List([[], [1], [1, 1], [2], [2, 2], [1, 2], [1, 2, 1, 2], [3],
                 [3, 1]], w -> function(Y)
      local y, i;
      y := Y[7]^0;
      for i in w do
        y := y * Y[[2, 5, 1][i]]^(Y[7]^2);
      od;
      return y * Y[7] * Y[4]^-1 * (Y[4]^Y[7])^-1;
    end);
  fi;
  res := [];
  seen := [];
  for shift in [0, 1, -1, 2, -2, 3, -3, 4] do
    pos := shift mod (n / 2 - r);
    if pos in seen then
      continue;
    fi;
    Add(seen, pos);
    for k in [2, 5] do
      for e in [1, -1] do
        Add(res, [shift, k, e]);
      od;
    od;
  od;
  res := List(res{[1 .. Minimum(8, Length(res))]}, w -> function(Y)
    local z, y;
    z := Y[7];
    y := Y[w[2]];
    if r = 1 then
      z := z * Y[4]^-1;
      y := y^Y[7];
    fi;
    return (y^(z^w[1]))^w[3] * z;
  end);
  if r = 1 then
    return Concatenation([Y -> Y[7] * Y[4]^-1], res);
  fi;
  return Concatenation([Y -> Y[7]], res);
end;

# The number of new doubling elements a GoingUp step for Omega over GF(3)
# from degree n >= 10 tries when RECOG.O_GoingUpCycleBasis fails, before it
# falls back to the pair transpositions
RECOG.O_GoingUpCycleRetries := 3;

# An element k of Omega^+(n,q), as a matrix and as the list of the Siegel
# transformations rho(p, z) whose product it is, mapping the rows of
# <rows> into the first ones of the n/2 pairs, row j into the first j
# pairs, for the standard form <J>: for each row, a rho(p, z) with p in
# pair j removes its part z beyond pair j, after a first rho(e_j, b) if the
# row has no component in pair j; later ones fix the earlier pairs.
RECOG.O_GoingUpTransport := function(rows, J, f)
  local n, I, k, ops, apply, j, lo, hi, v, tail, p;

  n := NrRows(J);
  I := IdentityMat(n, f);
  k := MutableCopyMat(I);
  ops := [];
  rows := ShallowCopy(rows);
  apply := function(p, z)
    local rho;
    rho := x -> x + (x * J * z - (x * J * p) * (z * J * z) / 2) * p
                - (x * J * p) * z;
    k := List(k, rho);
    rows := List(rows, rho);
    Add(ops, [p, z]);
  end;
  for j in [1 .. Length(rows)] do
    lo := 2 * j - 1;
    hi := 2 * j;
    v := rows[j];
    tail := ShallowCopy(v);
    tail{[1 .. hi]} := Zero(tail{[1 .. hi]});
    if IsZero(tail) then
      continue;
    fi;
    if IsZero(v[lo]) and IsZero(v[hi]) then
      apply(I[lo], I[PositionNonZero(tail * J)]);
      v := rows[j];
    fi;
    if IsZero(v[hi]) then
      p := I[hi];
    else
      p := I[lo];
    fi;
    tail := ShallowCopy(v);
    tail{[1 .. hi]} := Zero(tail{[1 .. hi]});
    apply(p, tail / (v * J * p));
    Assert(1, IsZero(rows[j]{[hi + 1 .. n]}));
  od;
  ConvertToMatrixRep(k, f);
  return rec( k := k, ops := ops );
end;

# Step 5 of the GoingUp step for Omega(W), q = 3, relative to a new basis
# of W, as proposed in the draft of [EHNPR] ('Constructing the enlarged
# group', two Siegel transformations). Let W = H + W_0 with W_0 the
# anisotropic part of W (0 unless n' = d and the type is - or o) and H of
# dimension 2m:
#  - h = x x^g~ for x from RECOG.O_GoingUpCycleWords, such that h fixes W_0
#    pointwise and the characteristic polynomial of h on H is squarefree;
#    as H(U) fixes U^perp, which contains W_0, h fixes W_0 if x fixes the
#    projection M of W_0 g~^-1 to U: x = k x0 k^-1 for x0 fixing the first
#    r = dim M pairs and k from RECOG.O_GoingUpTransport; as g~ fixes the
#    pivot pair, which is orthogonal to Fix(x) = U^perp + k(first r pairs),
#    Fix(x) meet Fix(x^g~) has dimension at least d - 2n + 4r + 2, so this
#    needs d + 3r + 2 <= 2n;
#  - e from RECOG.Form_IsotropicKrylovVector: E_0 = <e, e h, ...,
#    e h^(m-2)> is totally singular and beta(e, e h^(m-1)) <> 0;
#  - E = E_0 + <w> for a singular w in E_0^perp, and D = E meet E h =
#    <e h, ..., e h^(m-2)>; with the basis e, w of E/D and the dual basis
#    f_1, f_2 of E h/D, rho(u, z), u = w - f_1, z = e + f_2, maps f_1 to w
#    and f_2 to -e and fixes D, so k = h rho(u, z) stabilises E, with e
#    cyclic on E;
#  - with the companion basis b_i of E for k and a totally singular dual F,
#    rho(e, w') for w' in F corrects k on E to the signed cycle c of the
#    pair cycle, which then induces it on F modulo E; for p not dividing
#    m, c^p is the pair cycle relative to a suitable dual basis (as for Sp,
#    see RECOG.Form_GoingUpCycleBasis), otherwise a shear of the dual basis
#    leaves the remainder rho(e, y), y in E, so v_W = k rho(e, w' - y);
#  - the other standard generators are products of Siegel transformations
#    with centres in the first two new pairs and W_0, and their powers.
# <F> are the generators with memory standing for Y and g~, <g> is the
# matrix of g~ relative to the adapted basis, and <siegel>(x, y) the word
# for rho(x, y), x singular in W, y in W orthogonal to x, given as rows of
# length d. Returns fail if no candidate works, else the record of
# RECOG.GoingUpStep.
RECOG.O_GoingUpCycleBasis := function(std, F, g, siegel)
  local f, q, d, n, nn, type, aniso, nh, m, G, Ystd, emb, J, Jd, gi, M, tr,
        kw, km, x0, xw, xm, h, hW, chi, e, hw, E0, i, K, T, w, Yv, C, u, z,
        rho, k, orb, a, B, lam, solver, f0, Gr, fv, wR, c1, eps, p, next, sg,
        X, A, S, delta, tau, sv, half, y, vW, pad, basis, gamma, b1, f1, b2,
        f2, pw, tp, up, sp, dp, tt, lo, s, dl, w1, w2, gh, alpha, N, Wz, t;

  f := std.f;
  q := Size(f);
  d := std.d;
  n := std.n;
  nn := Minimum(2 * n - 2, d);
  type := "O+";
  if nn = d then
    type := std.type;
  fi;
  aniso := [];
  if type = "O-" then
    aniso := [d - 1, d];
  elif type = "O" then
    aniso := [d];
  fi;
  nh := nn - Length(aniso);
  m := nh / 2;
  if m <= n / 2 then
    # no new pair
    return fail;
  fi;
  G := F[Length(F)];
  Ystd := RECOG.ClassicalStandardGenerators("O+", n, f);
  emb := A -> RECOG.GoingUpEmbed(A, d, f);
  J := RECOG.ClassicalForm("O+", nh, f).gram;
  gi := g^-1;

  # the transport of M into the first pairs, as a matrix and a word
  M := gi{aniso}{[1 .. n]};
  M := Filtered(M, x -> not IsZero(x));
  tr := RECOG.O_GoingUpTransport(M, RECOG.ClassicalForm("O+", n, f).gram, f);
  pad := v -> ImmutableVector(f, Concatenation(v,
                  ListWithIdenticalEntries(d - Length(v), Zero(f))));
  kw := F[1]^0;
  for x0 in tr.ops do
    kw := kw * siegel(pad(x0[1]), pad(x0[2]));
  od;
  km := emb(tr.k);

  e := fail;
  for x0 in RECOG.O_GoingUpCycleWords(n, Length(M)) do
    xw := x0(F)^(kw^-1);
    xm := km * emb(x0(Ystd.all)) * km^-1;
    h := xm * gi * xm * g;
    if ForAny(aniso, i -> h[i] <> IdentityMat(d, f)[i]) then
      continue;
    fi;
    hW := h{[1 .. nh]}{[1 .. nh]};
    chi := CharacteristicPolynomial(hW);
    if DegreeOfLaurentPolynomial(Gcd(chi, Derivative(chi))) = 0 then
      e := RECOG.Form_IsotropicKrylovVector(hW, J, f, chi, "O+");
      if e <> fail then
        break;
      fi;
    fi;
  od;
  if e = fail then
    Info(InfoRecog_ClassicalNatural, 3, "GoingUp: no cycle word");
    return fail;
  fi;
  hw := xw * xw^G;
  # rho(x, y) on H
  rho := {x, y} -> List(IdentityMat(nh, f), v -> v + (v * J * y) * x
                        - (v * J * x) * (y + (y * J * y) / 2 * x));

  # E_0, a singular w completing it to E, and k = h rho(u, z)
  E0 := [e];
  for i in [2 .. m - 1] do
    Add(E0, E0[i - 1] * hW);
  od;
  K := NullspaceMat(J * TransposedMat(E0));
  T := BaseSteinitzVectors(K, E0).factorspace;
  w := First(Concatenation([T[2]], List(Elements(f), c -> T[1] + c * T[2])),
             x -> IsZero(x * J * x));
  Yv := [E0[m - 1] * hW, w * hW];
  C := [e, w] * J * TransposedMat(Yv);
  if RankMat(C) < 2 then
    return fail;
  fi;
  Yv := TransposedMat(C^-1) * Yv;
  u := w - Yv[1];
  z := e + Yv[2];
  Assert(1, IsZero(u * J * u) and IsZero(z * J * z) and IsZero(u * J * z));
  k := hW * rho(u, z);

  # the companion basis b_i of E for k, a dual F, and rho(e, wR)
  orb := [e];
  for i in [2 .. m] do
    Add(orb, orb[i - 1] * k);
  od;
  if RankMat(orb) < m then
    return fail;
  fi;
  a := SolutionMat(orb, orb[m] * k);
  eps := (-One(f))^(m - 1);
  if a[1] <> eps then
    return fail;
  fi;
  B := [e];
  for i in [1 .. m - 1] do
    Add(B, B[i] * k - a[m - i + 1] * e);
  od;
  lam := Concatenation([Zero(f)], List([1 .. m - 1], i -> -a[m - i + 1]));
  solver := RECOG.GoingUpSolver(TransposedMat(List(B, x -> x * J)));
  f0 := List(IdentityMat(m, f), solver);
  Gr := f0 * J * TransposedMat(f0);
  fv := List([1 .. m], j -> f0[j] - Gr[j] * B / 2);
  wR := lam * fv;
  c1 := k * rho(e, wR);
  Assert(1, ForAll([1 .. m - 1], i -> B[i] * c1 = B[i + 1])
            and B[m] * c1 = eps * B[1]);

  p := Characteristic(f);
  if m mod p <> 0 then
    # c^p, relative to b_i = e c^(p(i-1)) and f_i = f_1 c^(p(i-1)), with
    # beta(b_i, f_1) = delta_i1, after the Gram correction
    c1 := c1^p;
    B := [e];
    for i in [2 .. m] do
      Add(B, B[i - 1] * c1);
    od;
    solver := RECOG.GoingUpSolver(TransposedMat(List(B, x -> x * J)));
    fv := [solver(IdentityMat(m, f)[1])];
    for i in [2 .. m] do
      Add(fv, fv[i - 1] * c1);
    od;
    Gr := fv * J * TransposedMat(fv);
    fv := List([1 .. m], j -> fv[j] - Gr[j] * B / 2);
    Assert(1, List(Concatenation(List([1 .. m], i -> [B[i], fv[i]])),
                   x -> x * c1)
              = RECOG.ClassicalStandardGenerators("O+", nh, f).v
                * Concatenation(List([1 .. m], i -> [B[i], fv[i]])));
    vW := (hw * siegel(pad(u), pad(z)) * siegel(pad(e), pad(wR)))^p;
  else
    # f_i c = s_i f_(i+1) + sum_k X_ik b_k, s_m = eps, and A_ij = s_j
    # X_(i,j+1) is alternating; a shear f_i -> f_i + sum_k S_ik b_k,
    # S alternating, adds S_ij - s_i s_j S_(i+1,j+1). Along each cyclic
    # diagonal (i, i + delta), the remainder is moved to i = m (and to
    # i = delta for delta = m/2), so it lies in row and column m, where
    # c = v rho(e, y) with y in E
    next := i -> i mod m + 1;
    sg := ListWithIdenticalEntries(m, One(f));
    sg[m] := eps;
    X := List([1 .. m], i -> (fv[i] * c1 - sg[i] * fv[next(i)]) * J)
         * TransposedMat(fv);
    A := List([1 .. m], i -> List([1 .. m], j -> sg[j] * X[i][next(j)]));
    S := NullMat(m, m, f);
    for delta in [1 .. QuoInt(m, 2)] do
      half := 2 * delta = m;
      sv := [];
      sv[1] := Zero(f);
      for i in [1 .. m - 1] do
        if half and i = delta then
          break;
        fi;
        tau := sg[i] * sg[(i + delta - 1) mod m + 1];
        sv[i + 1] := (A[i][(i + delta - 1) mod m + 1] + sv[i]) / tau;
      od;
      if half then
        for i in [1 .. delta] do
          sv[i + delta] := -sv[i];
        od;
      fi;
      for i in [1 .. m] do
        S[i][(i + delta - 1) mod m + 1] := sv[i];
        if not half then
          S[(i + delta - 1) mod m + 1][i] := -sv[i];
        fi;
      od;
    od;
    fv := List([1 .. m], i -> fv[i] + S[i] * B);
    # c = v rho(e, y): f_1 rho(e, y) = f_1 - y + (b_1-part), and
    # f_1 v^-1 = eps f_m
    y := fv[1] - eps * fv[m] * c1;
    Assert(1, List(Concatenation(List([1 .. m], i -> [B[i], fv[i]])),
                   x -> x * c1 * rho(e, -y))
              = RECOG.ClassicalStandardGenerators("O+", nh, f).v
                * Concatenation(List([1 .. m], i -> [B[i], fv[i]])));
    vW := hw * siegel(pad(u), pad(z)) * siegel(pad(e), pad(wR - y));
  fi;

  basis := MutableCopyMat(IdentityMat(d, f));
  for i in [1 .. m] do
    basis[2 * i - 1] := pad(B[i]);
    basis[2 * i] := pad(fv[i]);
  od;
  Jd := RECOG.ClassicalForm(type, nn, f).gram;
  Assert(1, List(basis{[1 .. nn]}, x -> x{[1 .. nn]}) * Jd
              * TransposedMat(List(basis{[1 .. nn]}, x -> x{[1 .. nn]})) = Jd);

  # the generators on the first two pairs, with the Weyl words
  # A^c B^(1/c) A^c for Siegel transformations A, B, c in GF(p), and those
  # on the first pair and W_0 as in RECOG.O_GoingUpNewGenerators
  gamma := PrimitiveRoot(f);
  b1 := pad(B[1]);
  f1 := pad(fv[1]);
  b2 := pad(B[2]);
  f2 := pad(fv[2]);
  pw := {A, B, c} -> A^IntFFE(c) * B^IntFFE(c^-1) * A^IntFFE(c);
  tp := siegel(f1, -b2);
  up := siegel(b1, -f2);
  sp := pw(tp, up, One(f));
  if type = "O+" then
    dp := pw(tp, up, gamma) * sp^-1;
    tt := siegel(f1, f2);
    lo := siegel(b1, b2);
    s := pw(tt, lo, One(f));
    dl := pw(tt, lo, gamma) * s^-1;
    return rec( words := [s, tt, dl, sp, tp, dp, vW], basis := basis );
  fi;
  w1 := IdentityMat(d, f)[nh + 1];
  N := z -> -RECOG.FormQuadraticValue(RECOG.ClassicalForm(type, d, f), z);
  Wz := function(z)
    local r;
    r := siegel(f1, z);
    return r * siegel(b1, -z / N(z)) * r;
  end;
  if type = "O-" then
    w2 := IdentityMat(d, f)[nh + 2];
    t := siegel(f1, -w1);
    s := Wz(w1);
    gh := Z(q^2);
    alpha := gh^((q + 1) / 2);
    z := (gh + gh^q) / 2 * w1 + (gh - gh^q) / (2 * alpha) * w2;
  else
    t := siegel(f1, -2 * w1);
    s := Wz(2 * w1);
    z := 2 * gamma * w1;
  fi;
  return rec( words := [s, t, Wz(z) * s^-1, sp, vW], basis := basis );
end;

# Step 5 of the GoingUp step for orthogonal groups ([EHNPR], 'Constructing
# the enlarged group'): the standard generators of Omega(W), W = U + N,
# relative to the first n' vectors of the adapted basis, as words in the
# standard generators <Y> of Omega^+(U) and g~, whose matrix relative to the
# adapted basis is <g>. W has type + unless n' = d.
#
# The Siegel transformations rho(p, x) with p = e_m or f_m, the pair of the
# pivot space P, and x in A + N orthogonal to p are words in Y and g~:
# g~ fixes p, and A + A g~ = A + N, so for x = a_1 + a_2 g~ with a_i in A,
# rho(p, x) = rho(p, a_1) rho(p, a_2)^g~ ([EHNPR], proof of the generation
# of Omega(W)). With a = a_i, rho(p, a) = rho(p c^-1, a c^-1)^c for
# c = v^(m-1), which maps the first pair to the m-th, and rho(e_1, z) and
# rho(f_1, z) are products of root elements.
#
# The pair cycle of W is v_W = sigma_(m+1) sigma_(m+2)^-1 sigma_(m+3) ...
# sigma_(m')^(+-1) v_U, with m' the number of pairs of W and sigma_j the
# element e_m -> e_j, f_m -> f_j, e_j -> -e_m, f_j -> -f_m, which fixes the
# other basis vectors; the alternating exponents make the signs those of
# v_W. As the pairs m and j are hyperbolic and orthogonal,
#   sigma_j = rho(e_j, f_m) rho(e_m, -f_j) rho(e_j, f_m)
# by the factorisation of the pair transposition tau_j of [EHNPR], 'The
# standard generators of CL(W)', with the pairs m and j for j and j+1.
# [EHNPR] composes v_W from tau_(m'-1), ..., tau_m instead; these need
# Siegel transformations rho(x, .) with x in N, each of them conjugated
# from P by an element mapping x into P, whereas here rho(e_j, f_m) =
# rho(f_m, -e_j) and all Siegel transformations have their first vector in
# P.
#
# If n' = d and V has type - or o, the standard generators of that type
# are s, t, delta, u, v, with u = s' and v = v_W. With w_1 (and w_2) the
# anisotropic part, N(z) = -Q(z) for z in <w_1, w_2>, and
#   W(z) = rho(f_1, z) rho(e_1, -z/N(z)) rho(f_1, z),
# which maps e_1 to N(z) f_1 and f_1 to e_1/N(z) and acts as the reflection
# in z on <w_1, w_2>: for "O-", t = rho(f_1, -w_1), s = W(w_1) and
# delta = W(z) s^-1, where z = a w_1 + b w_2 for the primitive element
# g = a + b alpha of GF(q^2), alpha^2 = gamma, of the standard generators
# (see RECOG.OrthogonalStandardGenerators); for "O", t = rho(f_1, -2 w_1),
# s = W(2 w_1) and delta = W(2 gamma w_1) s^-1. On <w_1, w_2> identified
# with GF(q^2) by w_1 -> 1, w_2 -> alpha, Q(z) = -z z^q, W(z) s^-1 is
# multiplication by z^(q-1), and N(z) = z^(q+1); so delta is the case
# z = g. For "O-" and q even, the same holds with N(z) = Q(z), w_2 -> g and
# Q(z) = z z^q; there delta multiplies by g^(1-q), the case
# z = g^q = eta w_1 + w_2. [EHNPR] leaves these factorisations open ('The
# standard generators of CL(W)', part (3)).
# Over GF(3), the step first tries RECOG.O_GoingUpCycleBasis.
# Returns its record, or fail, so that the step is repeated with a new
# doubling element (see RECOG.O_GoingUpCycleRetries), or else the list of
# words, as elements with memory in generators standing for Y and g~.
RECOG.O_GoingUpNewGenerators := function(std, Y, R, g)
  local f, q, d, n, nn, m, F, gt, RF, e, cmat, c, solver, siegelU, siegelP,
        siegel1, Jd, move, toP, siegel, r, res, mm, v, j, sigma, type, w1, w2,
        gh, alpha, form, N, Wz, s, t, delta, z;

  f := std.f;
  q := Size(f);
  d := std.d;
  n := std.n;
  nn := Minimum(2 * n - 2, d);
  m := n / 2;
  F := GeneratorsWithMemory(ListWithIdenticalEntries(Length(Y) + 1, ()));
  gt := F[Length(F)];
  RF := RECOG.O_RootElements(F{[1 .. Length(Y)]}, n, f);
  e := IdentityMat(d, f);

  # c = v^(m-1) maps the first pair to the m-th; cmat is c^-1 on U
  c := RF.v^(m - 1);
  cmat := (RECOG.ClassicalStandardGenerators("O+", n, f).v)^(1 - m);

  # a_2 in A, as coordinates on its first n-2 basis vectors, with the same
  # projection to N as a vector x of A + N
  solver := RECOG.GoingUpSolver(g{[1 .. n - 2]}{[n + 1 .. nn]});

  # rho(p, a) for p = e_m (pos = n-1) or f_m (pos = n) and a in A, given by
  # its first n-2 coordinates: rho(e_1, z) is the product of the
  # See(j, -z_(e_j)) and Mj1(j, z_(f_j)), and rho(f_1, z) that of the
  # M1j(j, -z_(e_j)) and Sff(j, -z_(f_j)), z = a c^-1 in the pairs 2 to m
  siegelU := function(pos, a)
    local z, prod, j;
    z := Concatenation(a, [Zero(f), Zero(f)]) * cmat;
    prod := RECOG.Form_Product(RF, n);
    for j in [2 .. m] do
      if pos = n - 1 then
        prod.apply("See", j, -z[2 * j - 1]);
        prod.apply("Mj1", j, z[2 * j]);
      else
        prod.apply("M1j", j, -z[2 * j - 1]);
        prod.apply("Sff", j, -z[2 * j]);
      fi;
    od;
    return prod.word()^c;
  end;

  # rho(p, x) for p as for siegelU and x in A + N + <p>, given by its d
  # coordinates
  siegelP := function(pos, x)
    local a2, a1;
    Assert(1, IsZero(x[2 * n - 1 - pos]) and IsZero(x{[nn + 1 .. d]}));
    a2 := solver(x{[n + 1 .. nn]});
    a1 := x{[1 .. n - 2]} - (a2 * g{[1 .. n - 2]}){[1 .. n - 2]};
    return siegelU(pos, a1) * siegelU(pos, a2)^gt;
  end;

  # rho(e_1, x) (pos = n-1) or rho(f_1, x) (pos = n) for x in N, as
  # rho(e_m, x)^(c^-1) resp. rho(f_m, x)^(c^-1), since c fixes N
  siegel1 := {pos, x} -> siegelP(pos, x)^(c^-1);

  # rho(x, y) for x singular in W and y in W orthogonal to x, as
  # rho(x k, y k)^(k^-1), where k, a product of at most two rho(p, .) for
  # p in P, maps x to a multiple of e_m or f_m: rho(c p, y) = rho(p, c y).
  # k is kept for each x, with the maps [p, z] it is made of.
  Jd := RECOG.ClassicalForm(std.type, d, f).gram;
  move := function(x, p, z)
    local xp;
    xp := x * Jd * p;
    return x + (x * Jd * z - xp * (z * Jd * z) / 2) * p - xp * z;
  end;
  toP := [[], []];
  siegel := function(x, y)
    local pos, k, maps, xk, z, j, p, dual, scale;
    if IsZero(y) then
      return RF.one;
    fi;
    pos := Position(toP[1], x);
    if pos = fail then
      k := RF.one;
      maps := [];
      xk := x;
      if IsZero(xk{[n - 1, n]}) then
        z := xk * Jd;
        j := PositionNonZero(z);
        z := e[j] / z[j];
        k := siegelP(n - 1, z);
        Add(maps, [e[n - 1], z]);
        xk := move(xk, e[n - 1], z);
      fi;
      if IsZero(xk[n]) then
        p := n;
      else
        p := n - 1;
      fi;
      dual := 2 * n - 1 - p;
      scale := xk[dual];
      z := ShallowCopy(xk);
      z[n - 1] := Zero(f);
      z[n] := Zero(f);
      z := z / scale;
      if not IsZero(z) then
        k := k * siegelP(p, z);
        Add(maps, [e[p], z]);
        xk := move(xk, e[p], z);
      fi;
      Assert(1, xk = scale * e[dual]);
      Add(toP[1], x);
      Add(toP[2], rec( k := k, ki := k^-1, maps := maps, dual := dual,
                       scale := scale ));
      pos := Length(toP[1]);
    fi;
    k := toP[2][pos];
    for z in k.maps do
      y := move(y, z[1], z[2]);
    od;
    return k.k * siegelP(k.dual, k.scale * y) * k.ki;
  end;

  # over GF(3), a new doubling element is cheaper than the pair
  # transpositions below, if h of RECOG.O_GoingUpCycleBasis can have no
  # fixed points beyond the anisotropic part, of dimension r
  r := 0;
  if nn = d and std.type = "O" then
    r := 1;
  elif nn = d and std.type = "O-" then
    r := 2;
  fi;
  if q = 3 and nn + 3 * r + 2 <= 2 * n then
    res := RECOG.O_GoingUpCycleBasis(std, F, g, siegel);
    if not IsBound(std.cycleRetries) then
      std.cycleRetries := 0;
    fi;
    if res <> fail then
      std.cycleRetries := 0;
      return res;
    elif n >= 10 and std.cycleRetries < RECOG.O_GoingUpCycleRetries then
      std.cycleRetries := std.cycleRetries + 1;
      return fail;
    fi;
    std.cycleRetries := 0;
  fi;

  # the pair cycle of W, with mm pairs
  type := std.type;
  if nn < d then
    type := "O+";
  fi;
  mm := nn / 2;
  if type = "O-" then
    mm := mm - 1;
  elif type = "O" then
    mm := (nn - 1) / 2;
  fi;
  v := RF.v;
  for j in [mm, mm - 1 .. m + 1] do
    sigma := siegelP(n, -e[2 * j - 1]);
    sigma := sigma * siegelP(n - 1, -e[2 * j]) * sigma;
    if IsEvenInt(j - m) then
      sigma := sigma^-1;
    fi;
    v := sigma * v;
  od;
  if type = "O+" then
    return Concatenation(F{[1 .. 6]}, [v]);
  fi;

  # the generators on <e_1, f_1, w_1, w_2> resp. <e_1, f_1, w_1>
  w1 := e[2 * mm + 1];
  form := RECOG.ClassicalForm(type, d, f);
  N := z -> -RECOG.FormQuadraticValue(form, z);
  Wz := function(z)
    local r;
    r := siegel1(n, z);
    return r * siegel1(n - 1, -z / N(z)) * r;
  end;
  if type = "O-" then
    w2 := e[2 * mm + 2];
    t := siegel1(n, -w1);
    s := Wz(w1);
    if IsEvenInt(q) then
      z := RECOG.OrthogonalEta(q) * w1 + w2;
    else
      gh := Z(q^2);
      alpha := gh^((q + 1) / 2);
      z := (gh + gh^q) / 2 * w1 + (gh - gh^q) / (2 * alpha) * w2;
    fi;
  else
    t := siegel1(n, -2 * w1);
    s := Wz(2 * w1);
    z := 2 * Z(q) * w1;
  fi;
  delta := Wz(z) * s^-1;
  return [s, t, delta, F[4], v];
end;
