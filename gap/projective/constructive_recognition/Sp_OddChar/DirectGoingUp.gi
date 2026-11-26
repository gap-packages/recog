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
##  The direct GoingUp for symplectic groups in odd characteristic, from
##  Sp(4,q) to Sp(d,q) in one step, modelled on that for SL (see
##  ../SL/DirectGoingUp.gi).
##
##  Vectors are rows of coordinates relative to a standard basis
##  (e_1, f_1, ..., e_m, f_m), d = 2m, beta is the form of
##  RECOG.ClassicalForm, U = <e_1, f_1, e_2, f_2>, H = Sp(U) fixes
##  T = U^perp pointwise, and e = e_1. T(w, lambda) is the transvection
##  x -> x + lambda beta(x, w) w. For w in e^perp,
##
##      R(w): x -> x + beta(x, e) w + beta(x, w) e
##
##  is an isometry. These are the elements of Q, the unipotent radical of
##  the stabiliser of <e>, with R(w) R(w') = R(w + w' + beta(w, w')/2 e),
##  R(a e) = T(e, 2a), and R(w)^k = R(w k) for an isometry k fixing e. H
##  contains the R(w) with w in <e_1, e_2, f_2>. For a random g in
##  G = Sp(V):
##
##   1. Elements of Q. Let P_i be the projection of e g^-i to U along T.
##      The elements of H^(g^i) fixing e are the k = g^-i h g^i with h in
##      H fixing P_i, and for w in e^perp and A the projection of w g^-i
##      to U, w k = w + (A h - A) g^i. If beta(A, P_i) <> 0, then for each
##      D in U orthogonal to P_i there is one such h in the unipotent
##      radical of the stabiliser of <P_i> in H with A h = A + D: the
##      conjugate by b^-1 of an element of H meet Q, for b in H mapping
##      P_i to a multiple of e. So for K = k_1 ... k_r, as a word
##        K = g^-i_1 h_1 g^-(i_2 - i_1) h_2 ... h_r g^i_r,
##      R(s)^K = R(s + sum_j D_j g^i_j) for s = e_2 or f_2, with the h_j
##      determined by the D_j one after the other. A step with
##      beta(A, P_i) = 0 is left to a later product. The spaces
##      (U meet P_i^perp) g^i for about d/3 powers and <e_1, e_2, f_2>
##      span e^perp, so each element of Q is a product of few such
##      conjugates and an element of H, found by linear algebra on the
##      values beta(e g^j, .), 0 <= j < d. Like the P_i, these are terms
##      of linear recurrences, so g enters only through the orbit
##      e, e g, ..., e g^d.
##   2. e must be cyclic for g, and the characteristic polynomial chi of
##      g squarefree; the beta(e, e g^k), 0 < k <= d, decide both and give
##      chi. RECOG.Form_IsotropicKrylovPolynomial gives
##      e' = e p(g) with beta(e', e' g^j) = 0 for 0 <= j < m; it is
##      replaced by the first e' g^k with beta(e' g^k, e) <> 0, scaled so
##      that this is -1. Then z = s R(w_z) with
##      w_z = f_1 - e' - beta(f_1, e')/2 e maps e to e'.
##   3. chi = sum_k chi_k x^k is self-reciprocal. Let y = e' g^m,
##      kappa = beta(e', y), and R' the element of the radical for e'
##      which maps y to y + sum_(l<m) chi_(m+l) e' g^l. Then c' = g R' is
##      the cycle b'_1 -> ... -> b'_d -> -b'_1 on b'_i = e' c'^(i-1), where
##      beta(b'_i, b'_(m+i)) = kappa, and beta(b'_i, b'_j) = 0 for
##      |i - j| <> m: b'_i = e' g^(i-1) for i <= m, and
##      b'_(m+1+k) = b'_(m+k) g + chi_(m+k) e' for 0 < k < m. So
##      c = z c' z^-1 = z g z^-1 R, with R = z R' z^-1 in Q, is that cycle
##      on b_i = b'_i z^-1, b_1 = e.
##   4. The standard generators relative to (b_1, b_(m+1)/kappa, b_2,
##      b_(m+2)/kappa, ...): T(e, .) and T(b_(m+1), .) = T(e, .)^(c^m)
##      generate Sp(2,q) on the first pair, which gives s, t, delta and
##      w: b_1 -> b_(m+1) -> -b_1, and v = c w^-1. For w0 = e_2 or f_2
##      with beta(w0, b_2) <> 0, k = T(b_2, -1/beta(w0, b_2)) maps w0 to
##      w0 - b_2, so x = R(-b_2) is R(w0)^-1 R(w0)^k times a transvection
##      T(e, .), and u is a word in s, s^v and x.
##
##  So two elements of Q are needed, R(w_z) and R.
##
#############################################################################

# The number N of powers g^i which the direct GoingUp for Sp(<d>,<q>)
# tries: each gives three vectors, which behave like random vectors of
# e^perp, and d - 4 independent ones are needed
RECOG.Sp_DirectGoingUpPowers := {d, q} -> QuoInt(d, 3) + 6;

# The coefficients, lowest first, of the monic polynomial c of least degree
# with sum_j c_j s_(k+j) = 0 for all k, for a list <s> of 2n elements of
# the field <f> which satisfies such a recurrence of order at most n: for
# S = sum_k s_k x^(2n-1-k), the extended Euclidean algorithm for x^(2n) and
# S stops at c S = r mod x^(2n) with deg r < n.
RECOG.MinimalPolynomialOfSequence := function(f, s)
  local n, q, one, r0, r1, t0, t1, v, qr;

  n := Length(s) / 2;
  q := Size(f);
  one := One(f);
  r0 := ListWithIdenticalEntries(2 * n, Zero(f));
  Add(r0, one);
  r1 := Reversed(s);
  t0 := [Zero(f)];
  t1 := [one];
  for v in [r0, r1, t0, t1] do
    ConvertToVectorRep(v, q);
  od;
  ShrinkRowVector(r1);

  # r1 = t1 S mod x^(2n)
  while Length(r1) > n do
    qr := QuotRemCoeffs(r0, r1);
    r0 := r1;
    r1 := qr[2];
    ShrinkRowVector(r1);
    AddCoeffs(t0, ProductCoeffs(qr[1], t1), -one);
    ShrinkRowVector(t0);
    qr := t0;
    t0 := t1;
    t1 := qr;
  od;
  return PlainListCopy(t1 / t1[Length(t1)]);
end;

# The linear algebra of the direct GoingUp for the element <g> of
# Sp(<d>,q), q = Size(<f>) odd: the rows of <B> are a standard basis,
# <Bi> is its inverse, and the i <= <N> are tried. Returns a string
# saying why g is of no use, or a record with the following components:
#  - `basis`: the new standard basis, as a matrix
#  - `kappa`: kappa
#  - `P`: the P_i, 1 <= i <= N
#  - `Z`, `R`: for R(w_z) and R, a record with the list `rounds` of
#    records for the conjugates R(s)^K, with `sigma`, the index 3 or 4 of
#    s in U, and `steps`, the list of the [i, y] for the factors of K,
#    where h is the element R(y) for P_i instead of e; and with `rem`, the
#    vector w in U of the last factor R(w)
#  - `x`: a record with the index `w0` of w0 in U and `b` = beta(w0, b_2);
#    or, if that is 0 for both, with `a` = beta(w0, b_(m+2))/kappa, see
#    RECOG.Sp_DirectGoingUpWords
RECOG.Sp_DirectGoingUpData := function(f, d, g, B, Bi, N)
  local q, zero, m, J, J4, id4, e1, form, form4, K, i, top, BiU, seq, co,
        chi, x, Kinv, a, a0, o, extend, S, pc, k, val, vec, ppol, epp, eppB,
        yB, kappa, Omega, wz, applyZinv, P, phi, blocks, block, rowOf, perp,
        rows, where, D, T, solve, orbitCoords, toVector, plan, res, name,
        targets, bp, x1, x2, bt, wzo, c1, c2, basis, b2, bm2, w0, val2;

  q := Size(f);
  zero := Zero(f);
  m := d / 2;
  J := RECOG.ClassicalStandardForm("Sp", d, f);
  J4 := RECOG.ClassicalStandardForm("Sp", 4, f);
  id4 := IdentityMat(4, f);
  e1 := IdentityMat(d, f)[1];
  form := {v, w} -> v * J * w;
  form4 := {v, w} -> v * J4 * w;

  # K[k+1] = e g^k
  K := [B[1]];
  for i in [1 .. d] do
    K[i + 1] := K[i] * g;
  od;
  top := Remove(K);
  ConvertToMatrixRep(K, q);

  # phi_k = beta(e, e g^k) = -phi_(-k) is the coordinate of e g^k at f_1.
  # The beta(e g^-i, e g^j) = phi_(i+j), 0 <= i, j < d, form an invertible
  # matrix iff e is cyclic, that is, iff the phi_k satisfy no linear
  # recurrence of order less than d; then that of order d is
  # chi = x^d - sum_j a_j x^j. This rejects g without inverting K.
  BiU := TransposedMat(Bi){[1 .. 4]};
  seq := List(K, v -> v * BiU[2]);
  Add(seq, top * BiU[2]);
  co := RECOG.MinimalPolynomialOfSequence(f,
            Concatenation(-Reversed(seq{[2 .. d]}), seq));
  if Length(co) <= d then
    return "e is not cyclic";
  fi;
  chi := UnivariatePolynomial(f, co);
  if DegreeOfLaurentPolynomial(Gcd(chi, Derivative(chi))) > 0 then
    return "the characteristic polynomial has a repeated factor";
  fi;
  x := IndeterminateOfUnivariateRationalFunction(chi);
  Kinv := Inverse(K);
  a := -co{[1 .. d]};
  ConvertToVectorRep(a, q);
  a0 := a[1];

  # S[l][o+k] is the l-th coordinate of e g^k, -N <= k < N + d, from those
  # with 0 <= k < d
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
  S := List(BiU, c -> extend(List(K, v -> v * c)));

  # e' = e p(g) g^k / val, for the least k with beta(e p(g) g^k, e) <> 0
  pc := RECOG.Form_IsotropicKrylovPolynomial(seq, f, chi, "Sp");
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
  ppol := (UnivariatePolynomial(f, pc) * x^k) mod chi / val;
  epp := vec(ppol);
  eppB := epp * Bi;
  yB := vec((ppol * x^m) mod chi) * Bi;
  kappa := form(eppB, yB);

  # w_z, and the map v -> v z^-1 = v R(-w_z) s^-1
  wz := -eppB;
  wz[1] := wz[1] + eppB[1] / 2;
  wz[2] := zero;
  applyZinv := function(v)
    local w;
    w := v + v[2] * wz;
    w[1] := w[2];
    w[2] := form(v, wz) - v[1] - v[2] * wz[1];
    return w;
  end;

  # R' = R(w') for e' with w' = (sum_(0<l<m) chi_(m+l) e' g^l
  # + chi_m/2 e') / beta(y, e'), and R = R(w' z^-1)
  Omega := UnivariatePolynomial(f, Concatenation([co[m + 1] / 2],
                                                 co{[m + 2 .. d]}));
  targets := rec( Z := wz,
                  R := applyZinv(vec((ppol * Omega) mod chi) * Bi / -kappa) );

  # blocks[N+1+k] is the matrix on U of the projection of u g^k to U,
  # -N <= k <= N
  P := List([1 .. N], i -> List(S, s -> s[o - i]));
  phi := List([2 .. 4], l -> B[l] * Kinv);
  blocks := [];
  block := function(k)
    if not IsBound(blocks[N + 1 + k]) then
      blocks[N + 1 + k] := Concatenation([List(S, s -> s[o + k])],
          List(phi, v -> List(S, s -> v * s{[o + k .. o + k + d - 1]})));
    fi;
    return blocks[N + 1 + k];
  end;

  # the values beta(e g^j, D g^i), 0 <= j < d, for D <> 0 in U
  rowOf := function(i, D)
    local JD, r, l;
    JD := J4 * D;
    r := fail;
    for l in [1 .. 4] do
      if IsZero(JD[l]) then
        continue;
      elif r = fail then
        r := JD[l] * S[l]{[o - i .. o - i + d - 1]};
      else
        AddRowVector(r, S[l]{[o - i .. o - i + d - 1]}, JD[l]);
      fi;
    od;
    return r;
  end;
  # a basis of U meet p^perp for p in U
  perp := function(p)
    local Jp, l, res, lp, D;
    Jp := J4 * p;
    l := PositionNonZero(Jp);
    res := [];
    if l > 4 then
      return res;
    fi;
    for lp in Difference([1 .. 4], [l]) do
      D := ShallowCopy(id4[lp]);
      D[l] := -Jp[lp] / Jp[l];
      Add(res, D);
    od;
    return res;
  end;

  # w = sum_k c_k rows[k], as values at the e g^j
  rows := List([1, 3, 4], l -> rowOf(0, id4[l]));
  where := [];
  for i in [1 .. N] do
    for D in perp(P[i]) do
      Add(rows, rowOf(i, D));
      Add(where, [i, D]);
    od;
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
  # the values of a vector at the e g^j, and back
  orbitCoords := w -> K * (Bi * (J * w));
  toVector := vals -> -(J * (B * (Kinv * vals)));

  # the record for R(what), or fail
  plan := function(what)
    local sol, steps, k, last, rounds, total, todo, tried, rest, applied,
          ysteps, sigma, pair, i, D, A, cc, s, w, helper, rem;

    sol := solve(orbitCoords(what));
    if sol = fail then
      return fail;
    fi;
    steps := [];
    for k in [1 .. Length(where)] do
      if IsZero(sol[k + 3]) then
        continue;
      fi;
      last := Length(steps);
      if last > 0 and steps[last][1] = where[k][1] then
        steps[last][2] := steps[last][2] + sol[k + 3] * where[k][2];
      else
        Add(steps, [where[k][1], sol[k + 3] * where[k][2]]);
      fi;
    od;

    rounds := [];
    total := Zero(e1);
    todo := steps;
    tried := [];
    while todo <> [] do
      rest := [];
      applied := [];
      ysteps := [];
      sigma := fail;
      for pair in todo do
        i := pair[1];
        D := pair[2];
        if sigma = fail then
          sigma := First([3, 4],
                         s -> not IsZero(form4(block(-i)[s], P[i])));
          if sigma = fail then
            Add(rest, pair);
            continue;
          fi;
        fi;
        # the projection of (s + sum_j D_j g^i_j) g^-i to U
        A := block(-i)[sigma];
        for s in applied do
          A := A + s[2] * block(s[1] - i);
        od;
        cc := form4(A, P[i]);
        if IsZero(cc) then
          Add(rest, pair);
          continue;
        fi;
        Add(ysteps, [i, (D - form4(A, D) / (2 * cc) * P[i]) / cc]);
        Add(applied, pair);
      od;

      if sigma = fail then
        # no step can start a product: put one before them, and undo it
        helper := First(where, h -> not h[1] in tried and ForAny([3, 4],
                      s -> not IsZero(form4(block(-h[1])[s], P[h[1]]))));
        if helper = fail then
          return fail;
        fi;
        Add(tried, helper[1]);
        todo := Concatenation([helper], todo, [[helper[1], -helper[2]]]);
        continue;
      fi;

      w := rowOf(0, id4[sigma]);
      for s in applied do
        AddRowVector(w, rowOf(s[1], s[2]));
      od;
      w := toVector(w);
      total := total + w + form(total, w) / 2 * e1;
      Add(rounds, rec( sigma := sigma, steps := ysteps ));
      todo := rest;
    od;

    rem := what - total - form(total, what) / 2 * e1;
    Assert(1, IsZero(rem{[5 .. d]}) and IsZero(rem[2]));
    return rec( rounds := rounds, rem := rem{[1 .. 4]} );
  end;

  res := rec( kappa := kappa, P := P );
  for name in ["Z", "R"] do
    res.(name) := plan(targets.(name));
    if res.(name) = fail then
      return "span test failed";
    fi;
  od;

  # the b'_i
  bp := [epp];
  for i in [2 .. m] do
    bp[i] := bp[i - 1] * g;
  od;
  bp[m + 1] := bp[m] * g + co{[m + 1 .. d]} * bp;
  for k in [1 .. m - 1] do
    bp[m + 1 + k] := bp[m + k] * g + co[m + k + 1] * epp;
  od;
  ConvertToMatrixRep(bp, q);

  # b_i = b'_i z^-1: with the coordinates v_1, v_2 of v at e and f_1, and
  # w_z1 of w_z at e, v z^-1 = v + v_2 w_z + c (e + f_1)
  # + (beta(v, w_z) - 2 v_2) f_1 for c = v_2 - v_1 - v_2 w_z1
  x1 := bp * (Bi * e1);
  x2 := bp * (Bi * IdentityMat(d, f)[2]);
  bt := bp * (Bi * (J * wz));
  wzo := wz * B;
  c1 := x2 - x1 - wz[1] * x2;
  c2 := c1 - 2 * x2 + bt;
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

  # beta(e_2, v) = v_4 and beta(f_2, v) = -v_3
  b2 := basis[3] * Bi;
  bm2 := basis[4] * Bi;
  val := [b2[4], -b2[3]];
  val2 := [bm2[4], -bm2[3]];
  w0 := PositionNonZero(val);
  if w0 <= 2 then
    res.x := rec( w0 := w0 + 2, b := val[w0] );
  else
    w0 := PositionNonZero(val2);
    if w0 > 2 then
      return "b_2 and b_(m+2) are orthogonal to e_2 and f_2";
    fi;
    res.x := rec( w0 := w0 + 2, a := val2[w0] );
  fi;
  return res;
end;

# The words of the direct GoingUp for the record <data> of
# RECOG.Sp_DirectGoingUpData: <F> are generators with memory standing for
# the standard generators of H = Sp(4,q) and for g. Returns the standard
# generators of Sp(d,q) relative to data.basis.
RECOG.Sp_DirectGoingUpWords := function(f, d, data, F)
  local q, one, m, gamma, kappa, RF, id, RE, G, Gi, powers, power, times,
        radicals, radical, maps, map, links, link, element, id4, z, c, cm,
        Le, Lf, weyl, s, t, delta, v, w0, x, u, k;

  q := Size(f);
  one := One(f);
  m := d / 2;
  gamma := Z(q);
  kappa := data.kappa;
  id4 := IdentityMat(4, f);
  RF := RECOG.Sp_RootElements(F{[1 .. 6]}, 4, f);
  id := RF.one;
  RE := {kind, lambda} -> RECOG.Form_RootElement(RF, kind, 2, lambda);
  G := F[7];
  Gi := G^-1;

  # g^k for k <> 0, kept
  powers := rec( pos := [G], neg := [Gi] );
  power := function(k)
    local cache, x;
    cache := powers.pos;
    x := G;
    if k < 0 then
      cache := powers.neg;
      x := Gi;
      k := -k;
    fi;
    if not IsBound(cache[k]) then
      cache[k] := x^k;
    fi;
    return cache[k];
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

  # R(y) for y = (y_1, 0, y_3, y_4) in U, kept
  radicals := rec();
  radical := function(y)
    local w, key;
    w := [RECOG.Form_RootElementCode(RF, "See", 2, -y[3]),
          RECOG.Form_RootElementCode(RF, "Mj1", 2, y[4]),
          RECOG.Form_RootElementCode(RF, "Le", 2, 2 * y[1] - y[3] * y[4])];
    key := JoinStringsWithSeparator(List(w, c -> String(c[2])), "_");
    if not IsBound(radicals.(key)) then
      radicals.(key) := times(List(w, c -> c[1]));
    fi;
    return radicals.(key);
  end;

  # b_i in H with P_i b_i = lambda e, as a record with its word, inverse
  # and matrix, and lambda; b_0 = 1. Then h = b_i R(lambda y b_i) b_i^-1.
  maps := [];
  map := function(i)
    local elim, y;
    if i = 0 then
      return rec( word := id, inverse := id );
    elif not IsBound(maps[i]) then
      elim := RECOG.Form_Elimination(RF, data.P[i], []);
      y := elim.y;
      if IsZero(y[1]) then
        if not IsZero(y[2]) then
          elim.apply("Le", 1, one);
        elif not IsZero(y[3]) then
          elim.apply("Mj1", 2, one);
        else
          elim.apply("See", 2, one);
        fi;
      fi;
      elim.apply("M1j", 2, -y[3] / y[1]);
      elim.apply("Sff", 2, -y[4] / y[1]);
      elim.apply("Lf", 1, -y[2] / y[1]);
      maps[i] := elim.result();
      maps[i].inverse := maps[i].word^-1;
      maps[i].lambda := y[1];
    fi;
    return maps[i];
  end;
  # b_i^-1 g^(i-j) b_j, kept
  links := rec();
  link := function(i, j)
    local key;
    if i = j then
      return id;
    fi;
    key := Concatenation(String(i), "_", String(j));
    if not IsBound(links.(key)) then
      links.(key) := times([map(i).inverse, power(i - j), map(j).word]);
    fi;
    return links.(key);
  end;

  # R(w) for the record <target> of RECOG.Sp_DirectGoingUpData
  element := function(target)
    local res, round, K, last, step, b;
    res := [];
    for round in target.rounds do
      K := id;
      last := 0;
      for step in round.steps do
        b := map(step[1]);
        K := times([K, link(last, step[1]),
                    radical(b.lambda * (step[2] * b.mat))]);
        last := step[1];
      od;
      Add(res, radical(id4[round.sigma])^times([K, link(last, 0)]));
    od;
    Add(res, radical(target.rem));
    return times(res);
  end;

  z := F[1] * element(data.Z);
  c := z * G * z^-1 * element(data.R);

  # T(e, l), T(b_(m+1)/kappa, l), and the map b_1 -> l b_(m+1)/kappa,
  # b_(m+1)/kappa -> -b_1/l
  cm := c^m;
  Le := l -> RE("Le", l);
  Lf := l -> Le(l / kappa^2)^cm;
  weyl := l -> Lf(l) * Le(l^-1) * Lf(l);
  s := weyl(one);
  t := Lf(one);
  delta := weyl(gamma) * s^-1;
  v := c * weyl(kappa)^-1;

  # x = R(-b_2); if beta(w0, b_2) = 0 for w0 = e_2 and f_2, then with
  # a = beta(w0, b_(m+2))/kappa <> 0 the same for T(b_(m+2), .) gives
  # R(-b_(m+2)/kappa) = x^(s^v)
  w0 := radical(id4[data.x.w0]);
  if IsBound(data.x.b) then
    k := Le(-data.x.b^-1)^c;
    x := w0^-1 * w0^k * Le(-data.x.b);
  else
    k := Lf(-data.x.a^-1)^c;
    x := (w0^-1 * w0^k * Le(-data.x.a))^((s^v)^-1);
  fi;
  u := (x^-1)^s * x^(s^v) * (x^-1)^s * s^2;

  return [s, t, delta, u, x, v];
end;

# The direct GoingUp for Sp, q odd: <G> and <init> are as in RECOG.GoingUp,
# with init.n = 4, and so is the record returned, except that `bas` does
# not start with vectors of init.bas.
RECOG.Sp_DirectGoingUp := function(G, init)
  local f, d, bas, basi, N, gm, data, words;

  f := DefaultFieldOfMatrixGroup(G);
  d := DimensionOfMatrixGroup(G);
  if d = 4 then
    return rec( slp := init.slp, bas := init.bas );
  fi;
  bas := MutableCopyMat(init.bas);
  ConvertToMatrixRep(bas, f);
  basi := bas^-1;

  N := RECOG.Sp_DirectGoingUpPowers(d, Size(f));
  repeat
    gm := PseudoRandom(G);
    data := RECOG.Sp_DirectGoingUpData(f, d, StripMemory(gm), bas, basi, N);
    if IsString(data) then
      Info(InfoRecog_ClassicalNatural, 3, "GoingUp: ", data);
    fi;
  until IsRecord(data);

  words := RECOG.Sp_DirectGoingUpWords(f, d, data,
               GeneratorsWithMemory(ListWithIdenticalEntries(7, ())));
  return rec( slp := CompositionOfStraightLinePrograms(SLPOfElms(words),
                         IntegratedStraightLineProgram(
                             [init.slp, SLPOfElms([gm])])),
              bas := data.basis );
end;
