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
RECOG.Omega_RootElements := function(Y, n, f)
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
RECOG.Omega_GoingUpSeed := function(Y, n, p)
  local m;

  m := n / 2;
  if IsEvenInt(m) then
    return Y.s * Y.v;
  elif m mod p <> 0 then
    return Y.v;
  fi;
  return Y.v * Y.("s'");
end;

# The words x of RECOG.Omega_GoingUpCycleBasis in the standard generators Y of
# Omega^+(n,q), as functions of Y (words or matrices): x = z and
# x = (Y[k]^(z^shift))^e z with z = v_U, e = 1, -1, shift = 0, 1, -1, ...,
# 4 distinct modulo n/2, and Y[k] = t' (k = 5) or t (k = 2). Those with t'
# come first, as they give a squarefree characteristic polynomial more
# often.
RECOG.Omega_GoingUpCycleWords := function(n)
  local res, seen, shift, pos, k, e;

  res := [];
  seen := [];
  for shift in [0, 1, -1, 2, -2, 3, -3, 4] do
    pos := shift mod (n / 2);
    if pos in seen then
      continue;
    fi;
    Add(seen, pos);
    for k in [5, 2] do
      for e in [1, -1] do
        Add(res, [shift, k, e]);
      od;
    od;
  od;
  return Concatenation([Y -> Y[7]],
      List(res, w -> Y -> (Y[w[2]]^(Y[7]^w[1]))^w[3] * Y[7]));
end;

# The number of new doubling elements a GoingUp step for Omega from degree
# n >= 10 tries when RECOG.Omega_GoingUpCycleBasis fails, before it falls back
# to the pair transpositions
RECOG.Omega_GoingUpCycleRetries := 3;

# Step 5 of the GoingUp step for Omega(W), q odd, relative to a new basis
# of W, as proposed in the draft of [EHNPR] ('Constructing the enlarged
# group', two Siegel transformations). Let W = H + W_0 with W_0
# anisotropic of dimension r (0 unless n' = d and the type is - or o) and
# H hyperbolic with m pairs, and eps = (-1)^(m-1):
#  - h = x x^g~ for x from RECOG.Omega_GoingUpCycleWords, with squarefree
#    characteristic polynomial on W; for odd n', a simple factor x - 1;
#  - for r = 0, e from RECOG.Form_IsotropicKrylovVector: E_0 = <e, e h,
#    ..., e h^(m-2)> is totally singular and beta(e, e h^(m-1)) <> 0;
#    E = E_0 + <w> for a singular w in E_0^perp, and D = E meet E h =
#    <e h, ..., e h^(m-2)>; with the basis e, w of E/D and the dual basis
#    f_1, f_2 of E h/D, rho(u, z), u = w - f_1, z = e + f_2, maps f_1 to w
#    and f_2 to -e and fixes D, so k = h rho(u, z) stabilises E, with e
#    cyclic on E. Replacing w by c w multiplies the determinant of k on E
#    by c^2, and it is a square, as k is in Omega, so one c makes it 1;
#  - for r > 0, E = <e, ..., e h^(m-1)> is maximal totally singular. With
#    y = e h^m, c0 = beta(e, y), D = <e h, ..., e h^(m-1)> and A_1 a
#    complement of D in <D, e, y>^perp, anisotropic of dimension r: for
#    t in A_1 with Q(t) = -eps c0, u = e + eps y + t is singular,
#    z = (y - eps e) / c0 is orthogonal to it, and rho(u, z) fixes D and
#    maps y to eps e. So k = h rho(u, z) is the signed cycle on the
#    e h^i, with determinant 1 on E, and acts on E^perp / E = A_1 as h
#    followed by the reflection in t. That is in Omega(A_1), so h acts on
#    A_1 as a reflection in some t_0, and t = t_0 up to a scalar makes k
#    trivial on E^perp / E;
#  - with the companion basis b_i of E for k and a totally singular dual
#    F, rho(e, w') for w' in F corrects k on E to the signed cycle c of the
#    pair cycle. For r > 0, a in A = (E + F)^perp has a c = a + theta(a)
#    with theta(a) in E; as E = E (c - 1) + <b_1>, some A_2 = {a + psi(a)},
#    psi(a) in E, has a c = a + tau(a) b_1, and rho(e, -a_0) with
#    beta(a, a_0) = tau(a) makes c fix A_2 pointwise. Then a shear of the
#    dual basis in A_2^perp leaves the remainder rho(e, y'), y' in E, so
#    v_W = k rho(e, w' - a_0 - y');
#  - the other standard generators are products of Siegel transformations
#    with centres in the first two new pairs and W_0 = A_2.
# No fixed vectors of h in W are forced, except one for odd n' by parity:
# for x without fixed vectors on U, Fix(x) = U^perp, and
# U^perp meet U^perp g~ = W^perp.
# <F> are the generators with memory standing for Y and g~, <g> is the
# matrix of g~ relative to the adapted basis, and <siegel>(x, y) the word
# for rho(x, y), x singular in W, y in W orthogonal to x, given as rows of
# length d. Returns fail if no candidate works, else the record of
# RECOG.GoingUpStep.
RECOG.Omega_GoingUpCycleBasis := function(std, F, g, siegel)
  local f, q, p, d, n, nn, type, r, m, G, Ystd, emb, form, J, Q, gi, pad, X,
        dual, e, x0, xw, xm, h, hW, chi, hw, rho, eps, E0, i, K, T, w, first,
        res, lam, u, z, k, y, c0, D, A1, basis1, phi, t, mu, orb, a, B,
        solver, f0, fv, s, c1, A, CM, M1, th, sol, A2, taus, GA, a0, next,
        sg, XX, AA, S, delta, half, sv, tau, vW, basis, aniso, gamma, b1, f1,
        b2, f2, weyl, tp, up, sp, dp, tt, lo, ss, dl, w1, w2, N, Wz, gh,
        alpha, zz, tw;

  f := std.f;
  q := Size(f);
  p := Characteristic(f);
  d := std.d;
  n := std.n;
  nn := Minimum(2 * n - 2, d);
  type := "O+";
  if nn = d then
    type := std.type;
  fi;
  r := 0;
  if type = "O-" then
    r := 2;
  elif type = "O" then
    r := 1;
  fi;
  m := (nn - r) / 2;
  G := F[Length(F)];
  Ystd := RECOG.ClassicalStandardGenerators("O+", n, f);
  emb := A -> RECOG.GoingUpEmbed(A, d, f);
  form := RECOG.ClassicalForm(type, nn, f);
  J := form.gram;
  Q := y -> RECOG.FormQuadraticValue(form, y);
  # a totally singular dual of E = <B> from vectors f0 with
  # beta(B_i, f0_j) = delta_ij
  dual := {B, f0} -> List([1 .. Length(f0)],
                          j -> f0[j] - (f0[j] * J * TransposedMat(f0)) * B / 2);
  gi := g^-1;
  pad := v -> ImmutableVector(f, Concatenation(v,
                  ListWithIdenticalEntries(d - Length(v), Zero(f))));
  X := Indeterminate(f);

  e := fail;
  for x0 in RECOG.Omega_GoingUpCycleWords(n) do
    xm := emb(x0(Ystd.all));
    h := xm * gi * xm * g;
    hW := h{[1 .. nn]}{[1 .. nn]};
    chi := CharacteristicPolynomial(hW);
    if DegreeOfLaurentPolynomial(Gcd(chi, Derivative(chi))) = 0 then
      if r = 1 then
        e := RECOG.Form_IsotropicKrylovVector(hW, J, f, chi, "O");
      else
        e := RECOG.Form_IsotropicKrylovVector(hW, J, f, chi, "O+");
      fi;
      if e <> fail then
        xw := x0(F);
        break;
      fi;
    fi;
  od;
  if e = fail then
    Info(InfoRecog_ClassicalNatural, 3, "GoingUp: no cycle word");
    return fail;
  fi;
  hw := xw * xw^G;
  # rho(x, y) on W
  rho := {x, y} -> List(IdentityMat(nn, f), v -> v + (v * J * y) * x
                        - (v * J * x) * (y + Q(y) * x));
  eps := (-One(f))^(m - 1);

  if r = 0 then
    E0 := [e];
    for i in [2 .. m - 1] do
      Add(E0, E0[i - 1] * hW);
    od;
    K := NullspaceMat(J * TransposedMat(E0));
    T := BaseSteinitzVectors(K, E0).factorspace;
    if IsZero(Q(T[2])) then
      w := T[2];
    else
      res := RootsOfUPol(f, Q(T[2]) * X^2 + (T[1] * J * T[2]) * X + Q(T[1]));
      if res = [] then
        return fail;
      fi;
      w := T[1] + res[1] * T[2];
    fi;
    # u, z and k for w, and the coefficient of e in e k^m relative to the
    # e k^i, which is eps times the determinant of k on E
    first := function(w)
      local Yv, C, u, z, k, orb, i;
      Yv := [E0[m - 1] * hW, w * hW];
      C := [e, w] * J * TransposedMat(Yv);
      if RankMat(C) < 2 then
        return fail;
      fi;
      Yv := TransposedMat(C^-1) * Yv;
      u := w - Yv[1];
      z := e + Yv[2];
      k := hW * rho(u, z);
      orb := [e];
      for i in [2 .. m] do
        Add(orb, orb[i - 1] * k);
      od;
      if RankMat(orb) < m then
        return fail;
      fi;
      return rec( u := u, z := z, k := k,
                  a0 := SolutionMat(orb, orb[m] * k)[1] );
    end;
    res := first(w);
    if res = fail then
      return fail;
    elif res.a0 <> eps then
      lam := RootsOfUPol(f, X^2 - eps / res.a0);
      if lam = [] then
        return fail;
      fi;
      res := first(lam[1] * w);
      if res = fail or res.a0 <> eps then
        return fail;
      fi;
    fi;
    u := res.u;
    z := res.z;
    k := res.k;
  else
    E0 := [e];
    for i in [2 .. m] do
      Add(E0, E0[i - 1] * hW);
    od;
    y := E0[m] * hW;
    c0 := e * J * y;
    D := E0{[2 .. m]};
    K := NullspaceMat(J * TransposedMat(Concatenation(D, [e, y])));
    A1 := BaseSteinitzVectors(K, D).factorspace;
    if Length(A1) <> r or IsZero(c0) then
      return fail;
    fi;
    # the action of h on A_1: h maps A_1 into D^perp meet y^perp =
    # D + <y> + A_1
    basis1 := Concatenation(D, [y], A1);
    phi := a -> SolutionMat(basis1, a * hW){[m + 1 .. m + r]} * A1;
    if r = 2 then
      t := First(List(A1, a -> phi(a) - a), x -> not IsZero(x));
    else
      t := A1[1];
    fi;
    if t = fail then
      return fail;
    fi;
    mu := RootsOfUPol(f, X^2 + eps * c0 / Q(t));
    if mu = [] then
      return fail;
    fi;
    t := mu[1] * t;
    u := e + eps * y + t;
    z := (y - eps * e) / c0;
    k := hW * rho(u, z);
  fi;

  # the companion basis b_i of E for k, a totally singular dual F, and
  # rho(e, s), which corrects k on E to the signed cycle
  orb := [e];
  for i in [2 .. m] do
    Add(orb, orb[i - 1] * k);
  od;
  if RankMat(orb) < m then
    return fail;
  fi;
  a := SolutionMat(orb, orb[m] * k);
  if a = fail or a[1] <> eps then
    return fail;
  fi;
  B := [e];
  for i in [1 .. m - 1] do
    Add(B, B[i] * k - a[m - i + 1] * e);
  od;
  lam := Concatenation([Zero(f)], List([1 .. m - 1], i -> -a[m - i + 1]));
  solver := RECOG.GoingUpSolver(TransposedMat(List(B, x -> x * J)));
  f0 := List(IdentityMat(m, f), solver);
  fv := dual(B, f0);
  s := lam * fv;
  c1 := k * rho(e, s);
  Assert(1, ForAll([1 .. m - 1], i -> B[i] * c1 = B[i + 1])
            and B[m] * c1 = eps * B[1]);

  A2 := [];
  if r > 0 then
    # A_2, with a c = a + tau(a) b_1, from theta(a) = psi(a) (c - 1) +
    # tau(a) b_1, and a_0 with beta(a, a_0) = tau(a)
    A := NullspaceMat(J * TransposedMat(Concatenation(B, fv)));
    # c acts on E = <B> as the signed cycle
    CM := NullMat(m, m, f);
    for i in [1 .. m - 1] do
      CM[i][i + 1] := One(f);
    od;
    CM[m][1] := eps;
    M1 := Concatenation(CM - IdentityMat(m, f), [IdentityMat(m, f)[1]]);
    taus := [];
    for i in [1 .. r] do
      th := SolutionMat(B, A[i] * c1 - A[i]);
      if th = fail then
        return fail;
      fi;
      sol := SolutionMat(M1, -th);
      Add(A2, A[i] + sol{[1 .. m]} * B);
      Add(taus, -sol[m + 1]);
    od;
    GA := (A2 * J * TransposedMat(A2))^-1;
    a0 := (taus * GA) * A2;
    s := s - a0;
    c1 := c1 * rho(e, -a0);
    Assert(1, ForAll(A2, a -> a * c1 = a));
    # a totally singular dual of E in A_2^perp: A_2 is orthogonal to E, so
    # projecting f0 onto A_2^perp keeps beta(B_i, f0_j) = delta_ij
    f0 := f0 - (f0 * J * TransposedMat(A2)) * GA * A2;
    fv := dual(B, f0);
  fi;

  # f_i c = s_i f_(i+1) + sum_k X_ik b_k, s_m = eps, and A_ij = s_j
  # X_(i,j+1) is alternating; a shear f_i -> f_i + sum_k S_ik b_k,
  # S alternating, adds S_ij - s_i s_j S_(i+1,j+1). Along each cyclic
  # diagonal (i, i + delta), the remainder is moved to i = m (and to
  # i = delta for delta = m/2), so it lies in row and column m, where
  # c = v rho(e, y) with y in E
  next := i -> i mod m + 1;
  sg := ListWithIdenticalEntries(m, One(f));
  sg[m] := eps;
  XX := List([1 .. m], i -> (fv[i] * c1 - sg[i] * fv[next(i)]) * J)
        * TransposedMat(fv);
  AA := List([1 .. m], i -> List([1 .. m], j -> sg[j] * XX[i][next(j)]));
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
      sv[i + 1] := (AA[i][(i + delta - 1) mod m + 1] + sv[i]) / tau;
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
  s := s - y;
  c1 := c1 * rho(e, -y);

  basis := MutableCopyMat(IdentityMat(d, f));
  for i in [1 .. m] do
    basis[2 * i - 1] := pad(B[i]);
    basis[2 * i] := pad(fv[i]);
  od;
  if r > 0 then
    aniso := RECOG.FormAnisotropicBasis(form, A2, A2 * J);
    if aniso = fail then
      return fail;
    fi;
    for i in [1 .. r] do
      basis[2 * m + i] := pad(aniso[i]);
    od;
  fi;
  K := List(basis{[1 .. nn]}, x -> x{[1 .. nn]});
  if K * J * TransposedMat(K) <> J
     or K * c1 <> RECOG.ClassicalStandardGenerators(type, nn, f).v * K then
    Info(InfoRecog_ClassicalNatural, 3, "GoingUp: cycle basis check failed");
    return fail;
  fi;

  # the generators on the first two pairs, with the Weyl words
  # x(c) y(1/c) x(c) for Siegel transformations x(c) = rho(a, c b),
  # y(c) = rho(a', c b'), and those on the first pair and W_0 as in
  # RECOG.Omega_GoingUpNewGenerators; x(c) = x(1)^c for c in GF(p)
  gamma := PrimitiveRoot(f);
  b1 := pad(B[1]);
  f1 := pad(fv[1]);
  b2 := pad(B[2]);
  f2 := pad(fv[2]);
  weyl := function(xa, xb, x1, ya, yb, y1, c)
    local xc;
    if c in GF(p) then
      return x1^IntFFE(c) * y1^IntFFE(c^-1) * x1^IntFFE(c);
    fi;
    xc := siegel(xa, c * xb);
    return xc * siegel(ya, c^-1 * yb) * xc;
  end;
  tp := siegel(f1, -b2);
  up := siegel(b1, -f2);
  sp := weyl(f1, -b2, tp, b1, -f2, up, One(f));
  vW := hw * siegel(pad(u), pad(z)) * siegel(pad(e), pad(s));
  if type = "O+" then
    dp := weyl(f1, -b2, tp, b1, -f2, up, gamma) * sp^-1;
    tt := siegel(f1, f2);
    lo := siegel(b1, b2);
    ss := weyl(f1, f2, tt, b1, b2, lo, One(f));
    dl := weyl(f1, f2, tt, b1, b2, lo, gamma) * ss^-1;
    return rec( words := [ss, tt, dl, sp, tp, dp, vW], basis := basis );
  fi;
  w1 := basis[2 * m + 1];
  N := v -> -RECOG.FormQuadraticValue(RECOG.ClassicalForm(type, d, f), v);
  Wz := function(v)
    local rr;
    rr := siegel(f1, v);
    return rr * siegel(b1, -v / N(v)) * rr;
  end;
  if type = "O-" then
    w2 := basis[2 * m + 2];
    tw := siegel(f1, -w1);
    ss := Wz(w1);
    gh := Z(q^2);
    alpha := gh^((q + 1) / 2);
    zz := (gh + gh^q) / 2 * w1 + (gh - gh^q) / (2 * alpha) * w2;
  else
    tw := siegel(f1, -2 * w1);
    ss := Wz(2 * w1);
    zz := 2 * gamma * w1;
  fi;
  return rec( words := [ss, tw, Wz(zz) * ss^-1, sp, vW], basis := basis );
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
# For q odd, the step first tries RECOG.Omega_GoingUpCycleBasis.
# Returns its record, or fail, so that the step is repeated with a new
# doubling element (see RECOG.Omega_GoingUpCycleRetries), or else the list of
# words, as elements with memory in generators standing for Y and g~.
RECOG.Omega_GoingUpNewGenerators := function(std, Y, R, g)
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
  RF := RECOG.Omega_RootElements(F{[1 .. Length(Y)]}, n, f);
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

  # a new doubling element is cheaper than the pair transpositions below,
  # if W has a new pair; r is the dimension of its anisotropic part
  r := 0;
  if nn = d and std.type = "O" then
    r := 1;
  elif nn = d and std.type = "O-" then
    r := 2;
  fi;
  if IsOddInt(q) and nn - r > n then
    res := RECOG.Omega_GoingUpCycleBasis(std, F, g, siegel);
    if not IsBound(std.cycleRetries) then
      std.cycleRetries := 0;
    fi;
    if res <> fail then
      std.cycleRetries := 0;
      return res;
    elif n >= 10 and std.cycleRetries < RECOG.Omega_GoingUpCycleRetries then
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
