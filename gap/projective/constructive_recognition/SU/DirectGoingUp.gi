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
##  The direct GoingUp for special unitary groups of even degree, from
##  SU(4,q0) to SU(d,q0) in one step, modelled on that for Sp (see
##  ../Sp_OddChar/DirectGoingUp.gi).
##
##  Vectors are rows of coordinates relative to a standard basis
##  (e_1, f_1, ..., e_m, f_m), d = 2m, over GF(q), q = q0^2, sigma is
##  c -> c^q0, N(x) = beta(x, x) for the form beta of RECOG.ClassicalForm,
##  U = <e_1, f_1, e_2, f_2>, H = SU(U) fixes T = U^perp pointwise, and
##  e = e_1. For isotropic p, z in p^perp and lam + lam^sigma = -N(z),
##
##      rho(p, z, lam): x -> x + beta(x, z) p - beta(x, p) z
##                             + lam beta(x, p) p
##
##  is the Siegel transformation of GoingUp.gi, with
##  rho(p, z, lam) rho(p, z', lam') = rho(p, z + z', lam + lam' - beta(z, z')),
##  rho(p, z + a p, lam) = rho(p, z, lam + a^sigma - a), and
##  rho(p, z, lam)^k = rho(pk, zk, lam) for isometries k. The rho(e, z, lam)
##  are the elements of Q, the unipotent radical of the stabiliser of <e>;
##  Q is not abelian, and its centre consists of the
##  T(e, lam) = rho(e, 0, lam). H contains those with z in <e_1, e_2, f_2>.
##  For a random g in G = SU(V):
##
##   1. Elements of Q. Let P_i be the projection of e g^-i to U along T.
##      The elements of H^(g^i) fixing e are the k = g^-i h g^i with h in
##      H fixing P_i, and for w in e^perp and A the projection of w g^-i
##      to U, w k = w + (A h - A) g^i. Unlike for Sp, P_i is not isotropic
##      in general, and h is taken from the radical of another vector:
##      p_i = e_1 + c f_2 or e_1 + c e_2 orthogonal to P_i, the image of e
##      under a root element b_i^-1 of H. For D in the plane
##      L_i = U meet <P_i, p_i>^perp and A with a = beta(A, p_i) <> 0 and
##      N(A + D) = N(A),
##        h = rho(p_i, -D / a, beta(A, D) / N(a))
##      fixes P_i and maps A to A + D; it is the conjugate by b_i^-1 of an
##      element of H meet Q. So for a seed s = zeta e_2 or zeta f_2 and
##      K = k_1 ... k_r, k_j = g^-i_j h_j g^i_j,
##        rho(e, s, 0)^K = rho(e, s + sum_j D_j g^i_j, 0),
##      provided each step keeps the norm of the vector reached so far,
##      one condition over GF(q0) per step, which Sp does not have. The
##      planes L_i g^i for about d/2 powers and <e_1, e_2, f_2> span
##      e^perp, so the vector of an element of Q is a sum of steps D_i g^i
##      and a vector of U, by linear algebra on the values beta(., e g^j),
##      0 <= j < d. The steps are distributed among chains K: the first
##      step of a chain determines zeta, and the chain takes each of the
##      remaining steps which keeps the norm when it is tried. The product
##      of the chains and an element of H meet Q is the element wanted;
##      its central part follows from the product formula. As for Sp, g
##      enters only through the orbit e, e g, ..., e g^d.
##   2. e must be cyclic for g, and the characteristic polynomial chi of
##      g squarefree. RECOG.Form_IsotropicKrylovPolynomial gives
##      e' = e p(g) with beta(e', e' g^j) = 0 for 0 <= j < m; it is
##      replaced by the first e' g^k with beta(e' g^k, e) <> 0, scaled so
##      that this is alpha = RECOG.UnitaryAlpha(GF(q)). Then
##      z = s rho(e, w_z, lam_z) with w_z = f_1 - e' / alpha and
##      lam_z = -beta(f_1, w_z) maps e to e'.
##   3. chi = sum_k chi_k x^k satisfies chi_k = chi_(d-k)^sigma. Let
##      y = e' g^m and kappa = beta(y, e'), which has trace 0. Then
##      c' = g rho(e', w', chi_m / kappa) with
##      w' = -(sum_(0<l<m) chi_(m+l) e' g^l) / kappa is the cycle
##      b'_1 -> ... -> b'_d -> -b'_1 on b'_i = e' c'^(i-1), where
##      beta(b'_(m+i), b'_i) = kappa, and beta(b'_i, b'_j) = 0 for
##      |i - j| <> m: b'_i = e' g^(i-1) for i <= m, and
##      b'_(m+1+k) = b'_(m+k) g + chi_(m-k) e' for 0 < k < m. So
##      c = z c' z^-1 = z g z^-1 rho(e, w' z^-1, chi_m / kappa) is that
##      cycle on b_i = b'_i z^-1, b_1 = e.
##   4. The standard generators relative to (b_1, b_(m+1)/kappa, b_2,
##      b_(m+2)/kappa, ...): T(e, .) and T(b_(m+1), .) = T(e, .)^(c^m)
##      generate SU(2,q0) on the first pair, which gives s, t, delta and
##      w: b_1 -> b_(m+1) -> -b_1, and v = c w^-1. For w0 = zeta e_2 or
##      zeta f_2, k = T(b_2, alpha) = T(e, alpha)^c maps w0 to
##      w0 + alpha beta(w0, b_2) b_2, so rho(e, a b_2, 0) is
##      rho(e, w0, 0)^-1 rho(e, w0, 0)^k times a transvection T(e, .), for
##      each a; x, y and u are words in three of these, s and s^v.
##
##  So two elements of Q are needed, rho(e, w_z, lam_z) and
##  rho(e, w' z^-1, chi_m / kappa).
##
#############################################################################

# The number N of powers g^i which the direct GoingUp for SU(<d>,q0),
# q0^2 = <q>, tries: each gives two vectors, which behave like random
# vectors of e^perp, and d - 4 independent ones are needed
RECOG.SU_DirectGoingUpPowers := {d, q} -> QuoInt(d, 2) + 6;

# The linear algebra of the direct GoingUp for the element <g> of
# SU(<d>,q0), q0^2 = Size(<f>): the rows of <B> are a standard basis, <Bi>
# is its inverse, and the i <= <N> are tried. Returns a string saying why
# g is of no use, or a record with the following components:
#  - `basis`: the new standard basis, as a matrix
#  - `kappa`: kappa
#  - `roots`: roots[i] is a record with `kind`, "Sff" or "M1j", and `c`,
#    for the root element b_i^-1 = kind(2, c) of H
#  - `Z`, `R`: for rho(e, w_z, lam_z) and rho(e, w' z^-1, chi_m / kappa),
#    a record with the list `chains` of records with the seed, as its
#    index `s0`, 3 or 4, in U and `zeta`, and the list `steps` of records
#    with `i`, `y` and `mu`, where h = b_i rho(e, y, mu) b_i^-1; and with
#    `rem` and `lam`, the last factor rho(e, rem, lam), rem in U
#  - `x`: a record with `pos`, 2 or m + 2, for b = b_pos, and `s0`, `beta0`
#    with beta(w0, b) = zeta beta0, see RECOG.SU_DirectGoingUpWords
RECOG.SU_DirectGoingUpData := function(f, d, g, B, Bi, N)
  local q, q0, one, zero, m, form, form4, J, J4, id4, conj, beta4, alpha,
        half, K, i, top, Kinv, a, a0, co, chi, x, o, extend, S, cS, pc, k,
        val, vec, ppol, epp, eppB, yB, kappa, wz, lamz, applyZinv, Omega,
        targets, rowOf, phi, proj, pw, P, c, toE, rows, where, D, T, solve,
        orbitCoords, stepFor, seedAcc, newChain, plan, res, name, bp, x1, x2,
        bt, wzo, c1, c2, basis, pos, bB, s0;

  q := Size(f);
  q0 := RootInt(q, 2);
  one := One(f);
  zero := Zero(f);
  m := d / 2;
  form := RECOG.ClassicalForm("SU", d, f);
  form4 := RECOG.ClassicalForm("SU", 4, f);
  J := form.gram;
  J4 := form4.gram;
  id4 := IdentityMat(4, f);
  conj := v -> RECOG.FormConjugate(form, v);
  beta4 := {v, w} -> RECOG.FormValue(form4, v, w);
  alpha := RECOG.UnitaryAlpha(f);
  half := RECOG.FormHalf(form);

  # K[k+1] = e g^k, and chi = x^d - sum_j a_j x^j
  K := [B[1]];
  for i in [1 .. d] do
    K[i + 1] := K[i] * g;
  od;
  top := Remove(K);
  ConvertToMatrixRep(K, q);
  Kinv := Inverse(K);
  if Kinv = fail then
    return "e is not cyclic";
  fi;
  a := top * Kinv;
  a0 := a[1];
  co := Concatenation(-PlainListCopy(a), [one]);
  chi := UnivariatePolynomial(f, co);
  if DegreeOfLaurentPolynomial(Gcd(chi, Derivative(chi))) > 0 then
    return "the characteristic polynomial has a repeated factor";
  fi;
  x := IndeterminateOfUnivariateRationalFunction(chi);

  # S[l][o+k] is the l-th coordinate of e g^k, -N <= k < N + d, from those
  # with 0 <= k < d, and cS[l] its image under sigma
  o := N + 1;
  extend := function(mid)
    local s, k;
    s := Concatenation(ListWithIdenticalEntries(N, zero), mid,
                       ListWithIdenticalEntries(N, zero));
    ConvertToVectorRep(s, q);
    for k in [d .. N + d - 1] do
      s[o + k] := a * s{[o + k - d .. o + k - 1]};
    od;
    for k in [-1, -2 .. -N] do
      s[o + k] := (s[o + k + d]
                   - a{[2 .. d]} * s{[o + k + 1 .. o + k + d - 1]}) / a0;
    od;
    return s;
  end;
  S := List(TransposedMat(Bi){[1 .. 4]}, c -> extend(List(K, v -> v * c)));
  cS := List(S, conj);

  # e' = e p(g) g^k alpha / val, for the least k with
  # val = beta(e p(g) g^k, e) <> 0
  pc := RECOG.Form_IsotropicKrylovPolynomial(
            List([0 .. d], i -> cS[2][o + i]), f, chi, "SU");
  if pc = fail then
    return "no isotropic orbit";
  fi;
  pc := Concatenation(pc, ListWithIdenticalEntries(d - Length(pc), zero));
  k := -1;
  repeat
    k := k + 1;
    val := pc * S[2]{[o + k .. o + k + d - 1]};
  until not IsZero(val) or k = N;
  if IsZero(val) then
    return "no isotropic orbit";
  fi;
  # the vector e r(g) for a polynomial r of degree less than d
  vec := function(r)
    local c;
    c := ShallowCopy(CoefficientsOfUnivariatePolynomial(r));
    Append(c, ListWithIdenticalEntries(d - Length(c), zero));
    ConvertToVectorRep(c, q);
    return c * K;
  end;
  ppol := (UnivariatePolynomial(f, pc) * x^k) mod chi * (alpha / val);
  epp := vec(ppol);
  eppB := epp * Bi;
  yB := vec((ppol * x^m) mod chi) * Bi;
  kappa := yB * J * conj(eppB);

  # w_z and lam_z, and the map v -> v z^-1 = v rho(e, -w_z, lam_z^sigma) s^-1
  wz := -eppB / alpha;
  wz[2] := zero;
  lamz := -wz[1]^q0;
  applyZinv := function(v)
    local w, c;
    w := v + v[2] * wz;
    c := w[1] + lamz^q0 * v[2] - v * J * conj(wz);
    w[1] := v[2] / alpha;
    w[2] := c * alpha^q0;
    return w;
  end;

  Omega := UnivariatePolynomial(f, Concatenation([zero], co{[m + 2 .. d]}));
  targets := rec(
      Z := rec( w := wz, lam := lamz ),
      R := rec( w := applyZinv(vec((ppol * Omega) mod chi) * Bi / -kappa),
                lam := co[m + 1] / kappa ) );

  # the values beta(D g^i, e g^j), 0 <= j < len, for D <> 0 in U
  rowOf := function(i, D, len)
    local DJ, r, l;
    DJ := D * J4;
    r := fail;
    for l in [1 .. 4] do
      if IsZero(DJ[l]) then
        continue;
      elif r = fail then
        r := DJ[l] * cS[l]{[o - i .. o - i + len - 1]};
      else
        AddRowVector(r, cS[l]{[o - i .. o - i + len - 1]}, DJ[l]);
      fi;
    od;
    return r;
  end;
  # the projection of w g^-i to U, for the list acc of the beta(w, e g^j),
  # 0 <= j < d + N: its values beta(., u) at the basis vectors u of U are
  # the beta(w, u g^i)
  phi := List([2 .. 4], l -> conj(B[l] * Kinv));
  proj := function(acc, i)
    local seg;
    seg := acc{[i + 1 .. i + d]};
    return Concatenation([seg[1]], List(phi, v -> v * seg)) * J4;
  end;

  # p_i = e_1 + c f_2 or e_1 + c e_2 orthogonal to P_i, the image of e
  # under b_i^-1 = Sff(2, c) resp. M1j(2, c), and a basis of L_i;
  # toE(i, y) = y b_i
  pw := [];
  for i in [1 .. N] do
    P := List(S, s -> s[o - i]);
    if not IsZero(P[3]) then
      c := -(P[2] / P[3])^q0;
      pw[i] := rec( kind := "Sff", c := c, p := [one, zero, zero, c] );
    elif not IsZero(P[4]) then
      c := -(P[2] / P[4])^q0;
      pw[i] := rec( kind := "M1j", c := c, p := [one, zero, c, zero] );
    else
      continue;
    fi;
    # plain lists: a vector compressed over GF(2) cannot be divided by an
    # element of GF(4)
    pw[i].L := List(NullspaceMat(TransposedMat([J4 * conj(P),
                                                J4 * conj(pw[i].p)])),
                    PlainListCopy);
  od;
  toE := function(i, y)
    local c;
    c := pw[i].c;
    y := ShallowCopy(y);
    if pw[i].kind = "Sff" then
      y[4] := y[4] - c * y[1];
      y[2] := y[2] + c^q0 * y[3];
    else
      y[3] := y[3] - c * y[1];
      y[2] := y[2] + c^q0 * y[4];
    fi;
    return y;
  end;

  # w = sum_k c_k rows[k], as values at the e g^j
  rows := List([1, 3, 4], l -> rowOf(0, id4[l], d));
  where := [];
  for i in [1 .. N] do
    if IsBound(pw[i]) then
      for D in pw[i].L do
        Add(rows, rowOf(i, D, d));
        Add(where, [i, D]);
      od;
    fi;
  od;
  ConvertToMatrixRep(rows, q);
  T := SemiEchelonMatTransformation(rows);
  solve := function(w)
    local c, col, k;
    w := ShallowCopy(w);
    c := ListWithIdenticalEntries(Length(T.vectors), zero);
    for col in [1 .. d] do
      k := T.heads[col];
      if k > 0 and not IsZero(w[col]) then
        c[k] := w[col];
        AddRowVector(w, T.vectors[k], -c[k]);
      fi;
    od;
    if not IsZero(w) then
      return fail;
    fi;
    ConvertToVectorRep(c, q);
    return c * T.coeffs;
  end;
  # the values beta(w, e g^j), 0 <= j < d
  orbitCoords := w -> conj(K * (Bi * conj(w * J)));

  # the record of the step D g^i from w, where A is the projection of
  # w g^-i to U, or fail
  stepFor := function(i, D, A)
    local b0, a;
    b0 := beta4(A, D);
    a := beta4(A, pw[i].p);
    if IsZero(a) or not IsZero(b0 + b0^q0 + beta4(D, D)) then
      return fail;
    fi;
    return rec( i := i, D := D, y := toE(i, -a^-1 * D),
                mu := b0 / a^(q0 + 1) );
  end;
  # a chain with the seed zeta e_2 or zeta f_2 and the step D g^i, or fail
  seedAcc := List([3, 4], s0 -> rowOf(0, id4[s0], d + N));
  newChain := function(i, D)
    local s0, A0, b0, zeta, st, acc;
    for s0 in [3, 4] do
      A0 := proj(seedAcc[s0 - 2], i);
      b0 := beta4(A0, D);
      if IsZero(b0) then
        continue;
      elif IsZero(beta4(D, D)) then
        zeta := alpha / b0;
      else
        zeta := -beta4(D, D) * half / b0;
      fi;
      st := stepFor(i, D, zeta * A0);
      if st <> fail then
        acc := zeta * seedAcc[s0 - 2];
        AddRowVector(acc, rowOf(i, D, d + N));
        return rec( s0 := s0, zeta := zeta, acc := acc, steps := [st] );
      fi;
    od;
    return fail;
  end;

  # the record for rho(e, target.w, target.lam), or a string
  plan := function(target)
    local sol, pending, k, last, chains, ch, pair, st, E, progress, rest,
          acc, lam, seeds, bY, r;

    sol := solve(orbitCoords(target.w));
    if sol = fail then
      return "span test failed";
    fi;
    pending := [];
    for k in [1 .. Length(where)] do
      if IsZero(sol[k + 3]) then
        continue;
      fi;
      last := Length(pending);
      if last > 0 and pending[last][1] = where[k][1] then
        pending[last][2] := pending[last][2] + sol[k + 3] * where[k][2];
      else
        Add(pending, [where[k][1], sol[k + 3] * where[k][2]]);
      fi;
    od;
    pending := Filtered(pending, pair -> not IsZero(pair[2]));

    # a chain starts with a step which has a seed, and takes each of the
    # remaining steps which keeps the norm when it is tried
    chains := [];
    while pending <> [] do
      ch := fail;
      for k in [1 .. Length(pending)] do
        ch := newChain(pending[k][1], pending[k][2]);
        if ch <> fail then
          Remove(pending, k);
          break;
        fi;
      od;
      if ch = fail then
        # no step can start a chain: put a step t p_j g^j before the first
        # one, and leave its negative to a later chain
        pair := pending[1];
        st := fail;
        for k in Cartesian(Difference([1 .. N], [pair[1]]),
                           [0 .. Minimum(q - 2, 2 * q0)]) do
          if not IsBound(pw[k[1]]) then
            continue;
          fi;
          E := Z(q)^k[2] * pw[k[1]].p;
          ch := newChain(k[1], E);
          if ch <> fail then
            st := stepFor(pair[1], pair[2], proj(ch.acc, pair[1]));
            if st <> fail then
              break;
            fi;
          fi;
        od;
        if st = fail then
          return "no seed";
        fi;
        Add(ch.steps, st);
        AddRowVector(ch.acc, rowOf(pair[1], pair[2], d + N));
        pending[1] := [k[1], -E];
      fi;
      Add(chains, ch);
      repeat
        progress := false;
        rest := [];
        for pair in pending do
          st := stepFor(pair[1], pair[2], proj(ch.acc, pair[1]));
          if st = fail then
            Add(rest, pair);
          else
            Add(ch.steps, st);
            AddRowVector(ch.acc, rowOf(pair[1], pair[2], d + N));
            progress := true;
          fi;
        od;
        pending := rest;
      until not progress or pending = [];
    od;

    # the product of the rho(e, y_c, 0), for the vectors y_c which the
    # chains reach, is rho(e, Y, lam) with Y their sum and
    # lam = -sum_(c<c') beta(y_c, y_c'); acc belongs to the partial sum
    acc := ListWithIdenticalEntries(d + N, zero);
    ConvertToVectorRep(acc, q);
    lam := zero;
    seeds := [zero, zero, zero, zero];
    for ch in chains do
      bY := ch.zeta^q0 * beta4(proj(acc, 0), id4[ch.s0]);
      for st in ch.steps do
        bY := bY + beta4(proj(acc, st.i), st.D);
      od;
      lam := lam - bY;
      AddRowVector(acc, ch.acc);
      seeds[ch.s0] := seeds[ch.s0] + ch.zeta;
      Unbind(ch.acc);
    od;

    # rho(e, Y, lam) rho(e, r, mu) = rho(e, Y + r, lam + mu - beta(Y, r))
    r := [sol[1], zero, sol[2], sol[3]] - seeds;
    return rec( chains := chains, rem := r,
                lam := target.lam - lam + beta4(target.w{[1 .. 4]}, r)
                       - beta4(r, r) );
  end;

  res := rec( kappa := kappa, roots := [] );
  for i in [1 .. N] do
    if IsBound(pw[i]) then
      res.roots[i] := rec( kind := pw[i].kind, c := pw[i].c );
    fi;
  od;
  for name in ["Z", "R"] do
    res.(name) := plan(targets.(name));
    if IsString(res.(name)) then
      return res.(name);
    fi;
  od;

  # the b'_i
  bp := [epp];
  for i in [2 .. m] do
    bp[i] := bp[i - 1] * g;
  od;
  bp[m + 1] := bp[m] * g + co{[m + 1 .. d]} * bp;
  for k in [1 .. m - 1] do
    bp[m + 1 + k] := bp[m + k] * g + co[m - k + 1] * epp;
  od;
  ConvertToMatrixRep(bp, q);

  # b_i = b'_i z^-1, as in applyZinv
  x1 := bp * (Bi * IdentityMat(d, f)[1]);
  x2 := bp * (Bi * IdentityMat(d, f)[2]);
  bt := bp * (Bi * (J * conj(wz)));
  wzo := wz * B;
  c1 := x2 / alpha - x1 - wz[1] * x2;
  c2 := alpha^q0 * (x1 + (wz[1] + lamz^q0) * x2 - bt) - x2;
  basis := [];
  for i in [1 .. d] do
    bp[i] := bp[i] + x2[i] * wzo + c1[i] * B[1] + c2[i] * B[2];
  od;
  for i in [1 .. m] do
    basis[2 * i - 1] := bp[i];
    basis[2 * i] := bp[m + i] / kappa;
  od;
  ConvertToMatrixRep(basis, q);
  res.basis := basis;

  # beta(e_2, b) = b_4^sigma and beta(f_2, b) = b_3^sigma
  for pos in [2, m + 2] do
    bB := bp[pos] * Bi;
    s0 := First([3, 4], s -> not IsZero(bB[7 - s]));
    if s0 <> fail then
      res.x := rec( pos := pos, s0 := s0, beta0 := bB[7 - s0]^q0 );
      return res;
    fi;
  od;
  return "b_2 and b_(m+2) are orthogonal to e_2 and f_2";
end;

# The words of the direct GoingUp for the record <data> of
# RECOG.SU_DirectGoingUpData: <F> are generators with memory standing for
# the standard generators of H = SU(4,q0) and for g. Returns the standard
# generators of SU(d,q0) relative to data.basis.
RECOG.SU_DirectGoingUpWords := function(f, d, data, F)
  local q, q0, one, m, gamma, alpha, kappa, RF, id, RE, G, powers, power,
        times, radicals, radical, seed, Xs, X, links, link, element, z, c,
        cm, Le, Lf, weyl, s, si, t, delta, v, s2, s2i, kx, kxi, rhoB, see, n,
        n1;

  q := Size(f);
  q0 := RootInt(q, 2);
  one := One(f);
  m := d / 2;
  gamma := Z(q);
  alpha := RECOG.UnitaryAlpha(f);
  kappa := data.kappa;
  RF := RECOG.SU_RootElements(F{[1 .. 7]}, 4, f);
  id := RF.one;
  RE := {kind, lambda} -> RECOG.Form_RootElement(RF, kind, 2, lambda);
  G := F[8];

  # g^i for i > 0, kept
  powers := [G];
  power := function(i)
    local j;
    for j in [Length(powers) + 1 .. i] do
      powers[j] := powers[j - 1] * G;
    od;
    return powers[i];
  end;

  # the product of the words in <list> other than id
  times := function(list)
    local res, y;
    res := id;
    for y in list do
      if IsIdenticalObj(res, id) then
        res := y;
      elif not IsIdenticalObj(y, id) then
        res := res * y;
      fi;
    od;
    return res;
  end;

  # rho(e, y, lam) for y = (y_1, 0, y_3, y_4) in U, kept
  radicals := rec();
  radical := function(y, lam)
    local w, key;
    w := [RECOG.Form_RootElementCode(RF, "See", 2, -y[3]),
          RECOG.Form_RootElementCode(RF, "Mj1", 2, y[4]^q0),
          RECOG.Form_RootElementCode(RF, "Le", 2,
              lam + y[1]^q0 - y[1] + y[3] * y[4]^q0)];
    key := JoinStringsWithSeparator(List(w, c -> String(c[2])), "_");
    if not IsBound(radicals.(key)) then
      radicals.(key) := times(List(w, c -> c[1]));
    fi;
    return radicals.(key);
  end;
  # rho(e, zeta s0, 0) for s0 = e_2 (3) or f_2 (4)
  seed := function(s0, zeta)
    if s0 = 3 then
      return RE("See", -zeta);
    fi;
    return RE("Mj1", zeta^q0);
  end;

  # X_i = b_i^-1 g^i for b_i in H with p_i b_i = e, and X_j X_i^-1, kept;
  # X_0 = 1
  Xs := [];
  X := function(i)
    if not IsBound(Xs[i]) then
      Xs[i] := rec( word := times([RE(data.roots[i].kind, data.roots[i].c),
                                   power(i)]) );
      Xs[i].inverse := Xs[i].word^-1;
    fi;
    return Xs[i];
  end;
  links := rec();
  link := function(j, i)
    local key;
    if j = 0 then
      return X(i).inverse;
    fi;
    key := Concatenation(String(j), "_", String(i));
    if not IsBound(links.(key)) then
      links.(key) := X(j).word * X(i).inverse;
    fi;
    return links.(key);
  end;

  # rho(e, w, lam) for the record <target> of RECOG.SU_DirectGoingUpData:
  # with h = b_i rho(e, y, mu) b_i^-1, a chain is the conjugate of its seed
  # by the product of the X_i^-1 rho(e, y, mu) X_i
  element := function(target)
    local res, ch, K, last, st;
    res := [];
    for ch in target.chains do
      K := id;
      last := 0;
      for st in ch.steps do
        K := times([K, link(last, st.i), radical(st.y, st.mu)]);
        last := st.i;
      od;
      K := K * X(last).word;
      Add(res, K^-1 * seed(ch.s0, ch.zeta) * K);
    od;
    Add(res, radical(target.rem, target.lam));
    return times(res);
  end;

  z := F[1] * element(data.Z);
  c := z * G * z^-1 * element(data.R);

  # T(e, l), T(b_(m+1)/kappa, l), and the map b_1 -> l b_(m+1)/kappa,
  # b_(m+1)/kappa -> -b_1/l, for l of trace 0
  cm := c^m;
  Le := l -> RE("Le", l);
  Lf := l -> Le(l / kappa^(q0 + 1))^cm;
  weyl := l -> Lf(l) * Le(-l^-1) * Lf(l);
  s := weyl(alpha);
  si := s^-1;
  t := Lf(alpha);
  delta := weyl(gamma^(q0 + 1) * alpha) * si;
  v := c * weyl(kappa)^-1;
  s2 := v^-1 * s * v;
  s2i := s2^-1;

  # rhoB(a) = rho(e, a b, 0) for b = b_2 or b_(m+2) = b_2 c^m, by
  # k = T(b, alpha) and w0 = zeta e_2 or zeta f_2 with
  # alpha beta(w0, b) = a
  if data.x.pos = 2 then
    kx := Le(alpha)^c;
  else
    kx := Le(alpha)^(cm * c);
  fi;
  kxi := kx^-1;
  rhoB := function(a)
    local S;
    S := seed(data.x.s0, a / (alpha * data.x.beta0));
    return S^-1 * kxi * S * kx * Le(-a^(q0 + 1) / alpha);
  end;
  # in the new basis, See(2, l) = rho(e, -l b_2, 0), and rho(e, a b_(m+2), 0)
  # = Mj1(2, (a kappa)^sigma) = See(2, -a kappa / alpha)^s2
  if data.x.pos = 2 then
    see := l -> rhoB(-l);
  else
    see := l -> s2 * rhoB(-l * alpha / kappa) * s2i;
  fi;
  # n(l) = M1j(2, l) Mj1(2, -1/l) M1j(2, l) maps e_1 -> l e_2 and
  # e_2 -> -e_1/l, with M1j(2, l) = See(2, l/alpha)^(s^-1) and
  # Mj1(2, l) = See(2, -l^q0/alpha)^s2
  n := function(l)
    local M1j;
    M1j := s * see(l / alpha) * si;
    return [M1j, M1j * s2i * see(l^-q0 / alpha) * s2 * M1j];
  end;
  n1 := n(one);

  return [s, t, delta, n1[2] * s^2, v, n1[1], n(gamma)[2] * n1[2]^-1];
end;

# The direct GoingUp for SU of even degree: <G> and <init> are as in
# RECOG.GoingUp, with init.n = 4, and so is the record returned, except
# that `bas` does not start with vectors of init.bas.
RECOG.SU_DirectGoingUp := function(G, init)
  local f, d, bas, basi, N, gm, data, words;

  f := DefaultFieldOfMatrixGroup(G);
  d := DimensionOfMatrixGroup(G);
  if d = 4 then
    return rec( slp := init.slp, bas := init.bas );
  fi;
  bas := MutableCopyMat(init.bas);
  ConvertToMatrixRep(bas, f);
  basi := bas^-1;

  N := RECOG.SU_DirectGoingUpPowers(d, Size(f));
  repeat
    gm := PseudoRandom(G);
    data := RECOG.SU_DirectGoingUpData(f, d, StripMemory(gm), bas, basi, N);
    if IsString(data) then
      Info(InfoRecog_ClassicalNatural, 3, "GoingUp: ", data);
    fi;
  until IsRecord(data);

  words := RECOG.SU_DirectGoingUpWords(f, d, data,
               GeneratorsWithMemory(ListWithIdenticalEntries(8, ())));
  return rec( slp := CompositionOfStraightLinePrograms(SLPOfElms(words),
                         IntegratedStraightLineProgram(
                             [init.slp, SLPOfElms([gm])])),
              bas := data.basis );
end;
