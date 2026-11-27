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
##  The direct GoingUp for special linear groups, from SL(2,q) to SL(d,q)
##  in one step, proposed by Till Eisenbrand for [EHNPR] (see
##  ../GoingDown.gi; alternative-goingup-sl.tex in its repository).
##
##  Let V = U + T with U = <e, f>, H = SL(U) fixing T pointwise, and
##  <x|e>, <x|f> the coordinates of x at e and f relative to a basis
##  (e, f, basis of T). For a functional w, T(w, x) is the transvection
##  z -> z + w(z) x; <.|f> is written f. For a random g in G = SL(V):
##
##   1. e must be a cyclic vector, e g^d = sum_j a_j e g^j. With b_1 = e
##      and b_(i+1) = b_i g - a_(d-i) e, and the functional w_R with
##      w_R(b_1) = 0 and w_R(b_(i+1)) = -a_(d-i), c = g T(w_R, e) is the
##      signed cycle b_1 -> ... -> b_d -> (-1)^(d-1) b_1.
##   2. Besides c, only L = T(w_2, e) is needed, for the coordinate w_2 at
##      b_2: it maps b_2 to b_2 + b_1 and fixes the other b_i. Both
##      transvections have centre e. H contains T(f, e). For i >= 1 let
##      e g^-i = alpha e + beta f + (a vector of T), and p_i =
##      (alpha e + beta f) g^i, so e - p_i lies in T g^i. The functional
##      y_i = (beta <.|e> - alpha <.|f>) g^-i vanishes on T g^i and on e,
##      and k_i(a) = T(a y_i, p_i) lies in H^(g^i), where it is the
##      conjugate of the transvection I + a (beta, -alpha)^T (alpha, beta)
##      of H, and fixes e. So T(phi, e)^(k_i(a)) =
##      T(phi - a phi(p_i) y_i, e) for every functional phi vanishing on
##      e, and for K = k_(i_1)(a_1) ... k_(i_r)(a_r), i_1 < ... < i_r,
##      T(f, e)^K = T(f + sum_j t_j y_(i_j), e), with the a_j determined by
##      the t_j one after the other. As a word,
##        K = g^-i_1 h_1 g^-(i_2 - i_1) h_2 ... h_r g^i_r
##      with h_j in H. An i with phi(p_i) = 0 for the current phi is left
##      to a later product, which it can start if <p_i|f> <> 0, so only
##      such i are used. The products of the T(., e) are sums of the
##      functionals.
##      [EHNPR] uses one commutator [T(f, e), k_i(a)] = T(t y_i, e) for
##      each i instead.
##   3. w_R and w_2 must be combinations of f and the y_i, which is
##      linear algebra on the values at the e g^j, 0 <= j < d: those of
##      y_i are beta <e g^(j-i)|e> - alpha <e g^(j-i)|f>. So g enters
##      only through the orbit e, e g, ..., e g^d (see
##      RECOG.SL_DirectGoingUpData).
##   4. The standard generators relative to the b_i, up to signs, are
##      short words in c, L and H.
##
#############################################################################

# The number N of powers g^i which the direct GoingUp for SL(<d>,<q>)
# tries: it needs d - 2 independent y_i with <p_i|f> <> 0, which behave
# like random vectors; e g^-i has alpha = beta = 0 for one i in q^2, and
# <p_i|f> = 0 for one in q of the others
RECOG.SL_DirectGoingUpPowers := {d, q} ->
    QuoInt((d + 20) * q^3, (q - 1)^2 * (q + 1)) + 10;

# The linear algebra of the direct GoingUp for the element <g> of
# SL(<d>,q), q = Size(<f>): <e> and <fv> are the vectors e and f, <c1> and
# <c2> the functionals <.|e> and <.|f>, as vectors, and the i <= <N> are
# tried. Only the orbit e, e g, ..., e g^d is computed: the sequences
# <e g^k|e> and <e g^k|f>, k in Z, satisfy the linear recurrence with the
# characteristic polynomial x^d - sum_j a_j x^j of g, and f is a
# combination of the e g^j.
# Returns fail if e is not cyclic for g, false if w_R or w_2 is no
# combination of f and the y_i, as happens if g leaves a subspace of T
# invariant, and otherwise a record with the following components:
#  - `basis`: the b_i, as a matrix
#  - `alpha`, `beta`: alpha and beta for 1 <= i <= N
#  - `E1`, `E2`, `F1`, `F2`: <e g^k|e>, <e g^k|f>, <f g^k|e> and
#    <f g^k|f> for 1 <= k <= N
#  - `D0`: <p_i|f> for 1 <= i <= N
#  - `R`, `L`: for w_R and w_2, a record with the coefficient `lambda` of
#    f and the list `terms` of the [i, t] with t <> 0 the coefficient of
#    y_i, by increasing i
#  - `lambda2`: w_2(f)
RECOG.SL_DirectGoingUpData := function(f, d, g, e, fv, c1, c2, N)
  local q, one, zero, K, i, top, Kinv, a, a0, phi, o, extend, E1, E2, alpha,
        beta, F1, F2, D0, cand, row, rows, solveL, xs, r, sols, T, solve,
        res, k, sol, Lmat;

  q := Size(f);
  one := One(f);
  zero := Zero(f);

  # K[k+1] = e g^k
  K := [e];
  for i in [1 .. d] do
    K[i + 1] := K[i] * g;
  od;
  top := Remove(K);
  ConvertToMatrixRep(K, q);
  Kinv := Inverse(K);
  if Kinv = fail then
    return fail;
  fi;
  # a[j+1] = a_j, and f = sum_j phi[j+1] e g^j
  a := top * Kinv;
  a0 := a[1];
  phi := fv * Kinv;

  # s[o+k] for -N <= k < N + d, from the s[o+k] with 0 <= k < d
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
  E1 := extend(List(K, v -> v * c1));
  E2 := extend(List(K, v -> v * c2));
  alpha := List([1 .. N], i -> E1[o - i]);
  beta := List([1 .. N], i -> E2[o - i]);
  F1 := List([1 .. N], k -> phi * E1{[o + k .. o + k + d - 1]});
  F2 := List([1 .. N], k -> phi * E2{[o + k .. o + k + d - 1]});
  D0 := List([1 .. N], i -> alpha[i] * E2[o + i] + beta[i] * F2[i]);
  cand := Filtered([1 .. N], i -> not IsZero(D0[i]));
  res := rec( alpha := alpha, beta := beta,
              E1 := PlainListCopy(E1{[o + 1 .. o + N]}),
              E2 := PlainListCopy(E2{[o + 1 .. o + N]}),
              F1 := F1, F2 := F2, D0 := D0 );

  # the values of y_i at the e g^j, 0 <= j < d
  row := i -> beta[i] * E1{[o - i .. o + d - 1 - i]}
              - alpha[i] * E2{[o - i .. o + d - 1 - i]};

  # the values x of a functional at the e g^j from its values r at the
  # b_k = e g^(k-1) - sum_(j<k) a_(d-k+j) e g^(j-1)
  solveL := function(r)
    local x, k;
    x := ShallowCopy(r);
    ConvertToVectorRep(x, q);
    for k in [2 .. d] do
      x[k] := r[k] + a{[d - k + 2 .. d]} * x{[1 .. k - 1]};
    od;
    return x;
  end;
  # for w_R and w_2
  r := ListWithIdenticalEntries(d, zero);
  r[2] := one;
  xs := [solveL(Concatenation([zero], List([2 .. d], k -> -a[d - k + 2]))),
         solveL(r)];

  # w = lambda f + sum_i t_i y_i
  rows := Concatenation([E2{[o .. o + d - 1]}], List(cand, row));
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
  sols := List(xs, solve);
  if fail in sols then
    return false;
  fi;

  res.lambda2 := phi * xs[2];
  for k in [1, 2] do
    sol := sols[k];
    res.(["R", "L"][k]) := rec( lambda := sol[1],
        terms := List(Filtered([1 .. Length(sol) - 1],
                               j -> not IsZero(sol[j + 1])),
                      j -> [cand[j], sol[j + 1]]) );
  od;

  # the b_k from the e g^j; plain lists, as Concatenation is slow for
  # compressed vectors
  a := -PlainListCopy(a);
  Lmat := List([1 .. d], k -> Concatenation(a{[d - k + 2 .. d]}, [one],
                                 ListWithIdenticalEntries(d - k, zero)));
  ConvertToMatrixRep(Lmat, q);
  res.basis := Lmat * K;
  return res;
end;

# The words of the direct GoingUp for the record <data> of
# RECOG.SL_DirectGoingUpData: <F> are generators with memory standing for
# the standard generators of H = SL(2,q) and for g. Returns a record with
# the following components:
#  - `words`: the standard generators of SL(d,q) relative to `basis`
#  - `basis`: the b_i, for odd d with alternating signs, as a matrix
RECOG.SL_DirectGoingUpWords := function(f, d, data, F)
  local q, p, one, id, gamma, RF, E, G, Gi, tfe, power, gip, gp, hwords,
        hword, transvection, R, L, c, cp, A, getA, top, U1, P, Lpower, U, D,
        basis, i;

  q := Size(f);
  p := Characteristic(f);
  one := One(f);
  gamma := Z(q);
  RF := RECOG.SL_RootElements(F{[1 .. 5]}, 2, f);
  E := {i, j, lambda} -> RECOG.SL_ElementaryMatrix(RF, i, j, lambda);
  id := RF.one;
  G := F[6];
  Gi := G^-1;
  # T(f, e)
  tfe := E(2, 1, one);

  # x^k for k > 0, kept in cache
  power := function(cache, x, k)
    if not IsBound(cache[k]) then
      cache[k] := x^k;
    fi;
    return cache[k];
  end;
  gip := [Gi];
  gp := [G];
  cp := [];

  # the transvection I + a (beta, -alpha)^T (alpha, beta) of H
  hwords := rec();
  hword := function(alpha, beta, a)
    local rho, mu, key, er;
    if IsZero(alpha) then
      return E(1, 2, a * beta^2);
    elif IsZero(beta) then
      return E(2, 1, -a * alpha^2);
    fi;
    rho := RECOG.SL_ElementaryMatrixCode(RF, 1, 2, beta / alpha);
    mu := RECOG.SL_ElementaryMatrixCode(RF, 2, 1, -a * alpha^2);
    key := Concatenation(String(rho[2]), "_", String(mu[2]));
    if not IsBound(hwords.(key)) then
      er := Concatenation("i", String(rho[2]));
      if not IsBound(hwords.(er)) then
        hwords.(er) := rho[1]^-1;
      fi;
      hwords.(key) := hwords.(er) * mu[1] * rho[1];
    fi;
    return hwords.(key);
  end;

  # T(lambda f + sum_j t_j y_(i_j), e) for target.terms = [[i_j, t_j]]: each
  # round is one product K, and leaves the terms with phi(p_i) = 0 to the
  # next round
  transvection := function(target)
    local res, count, todo, rest, seg, last, J, TB, TA, pair, i, t, D, idx;
    res := id;
    count := 0;
    todo := target.terms;
    while todo <> [] do
      rest := [];
      seg := fail;
      for pair in todo do
        i := pair[1];
        t := pair[2];
        if seg = fail then
          D := data.D0[i];
          J := [];
          TB := [];
          TA := [];
          seg := power(gip, Gi, i);
        else
          # phi(p_i) for phi = f + sum_j t_j y_j over the j of this round
          idx := i - J;
          D := data.D0[i]
               + data.alpha[i] * (TB * data.E1{idx} - TA * data.E2{idx})
               + data.beta[i] * (TB * data.F1{idx} - TA * data.F2{idx});
          if IsZero(D) then
            Add(rest, pair);
            continue;
          fi;
          seg := seg * power(gip, Gi, i - last);
        fi;
        seg := seg * hword(data.alpha[i], data.beta[i], -t / D);
        Add(J, i);
        Add(TB, t * data.beta[i]);
        Add(TA, t * data.alpha[i]);
        last := i;
      od;
      res := res * tfe^(seg * power(gp, G, last));
      count := count + 1;
      todo := rest;
    od;
    return E(2, 1, target.lambda - count * one) * res;
  end;

  R := transvection(data.R);
  L := transvection(data.L);
  c := G * R;

  # A[k] maps b_(k+1) to b_(k+1) + b_1: A[i+j] = [A[j]^(c^i), A[i]]
  A := [L];
  getA := function(k)
    local i;
    if not IsBound(A[k]) then
      i := QuoInt(k, 2);
      A[k] := Comm(getA(k - i)^power(cp, c, i), getA(i));
    fi;
    return A[k];
  end;
  # U1 maps b_1 to b_1 + b_2, as b_d c = (-1)^(d-1) b_1
  top := getA(d - 1);
  if IsEvenInt(d) then
    top := top^-1;
  fi;
  U1 := top^c;
  # P maps b_1 to b_2 and b_2 to -b_1
  P := U1 * L^-1 * U1;

  # T(a w_2, e), which maps b_2 to b_2 + a b_1: for h = diag(a, 1/a) in H,
  # L^h = T(a w_2 + lambda2 a (a - 1) f, e)
  Lpower := function(a)
    local k;
    if a in GF(p) then
      k := IntFFE(a);
      if 2 * k > p then
        k := k - p;
      fi;
      return L^k;
    fi;
    return L^(F[3]^LogFFE(a, gamma)) * E(2, 1, -data.lambda2 * a * (a - one));
  end;
  # b_1 -> b_1 + a b_2
  U := a -> Lpower(-a)^P;
  D := U(gamma) * Lpower(-gamma^-1) * U(gamma) * P^-1;

  if IsEvenInt(d) then
    return rec( words := [P, U1, D, c^2 * P^2, P^(c^2) * P^c * P],
                basis := data.basis );
  fi;
  basis := MutableCopyMat(data.basis);
  for i in [2, 4 .. d - 1] do
    basis[i] := -basis[i];
  od;
  return rec( words := [P^-1, U(-one), D, c^-1, id], basis := basis );
end;

# The direct GoingUp for SL: <G> and <init> are as in RECOG.GoingUp, with
# init.n = 2, and so is the record returned.
RECOG.SL_DirectGoingUp := function(G, init)
  local f, d, q, bas, cols, N, gm, data, res;

  f := DefaultFieldOfMatrixGroup(G);
  d := DimensionOfMatrixGroup(G);
  q := Size(f);
  bas := MutableCopyMat(init.bas);
  ConvertToMatrixRep(bas, f);
  # the functionals <.|e> and <.|f>
  cols := TransposedMat(bas^-1){[1, 2]};

  N := RECOG.SL_DirectGoingUpPowers(d, q);
  repeat
    gm := PseudoRandom(G);
    data := RECOG.SL_DirectGoingUpData(f, d, StripMemory(gm), bas[1], bas[2],
                                       cols[1], cols[2], N);
    if data = fail then
      Info(InfoRecog_ClassicalNatural, 3, "GoingUp: e is not cyclic");
    elif data = false then
      Info(InfoRecog_ClassicalNatural, 3, "GoingUp: span test failed");
    fi;
  until IsRecord(data);

  res := RECOG.SL_DirectGoingUpWords(f, d, data,
             GeneratorsWithMemory(ListWithIdenticalEntries(6, ())));
  return rec( slp := CompositionOfStraightLinePrograms(SLPOfElms(res.words),
                         IntegratedStraightLineProgram(
                             [init.slp, SLPOfElms([gm])])),
              bas := res.basis );
end;
