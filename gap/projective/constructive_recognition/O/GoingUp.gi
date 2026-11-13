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
##  'GoingUp algorithm', specific to orthogonal groups, q odd.
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

# Root elements of Omega^+(<n>,q), q = Size(<f>) odd, n >= 4, as words in
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
# z = g. [EHNPR] leaves these factorisations open ('The standard
# generators of CL(W)', part (3)).
# Returns the list of words, as elements with memory in generators standing
# for Y and g~.
RECOG.O_GoingUpNewGenerators := function(std, Y, R, g)
  local f, q, d, n, nn, m, F, gt, RF, e, cmat, c, solver, siegelU, siegelP,
        siegel1, mm, v, j, sigma, type, w1, w2, gh, alpha, N, Wz, s, t,
        delta, z;

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
    local z, res, j;
    z := Concatenation(a, [Zero(f), Zero(f)]) * cmat;
    res := RF.one;
    for j in [2 .. m] do
      if pos = n - 1 then
        res := res * RECOG.Form_RootElement(RF, "See", j, -z[2 * j - 1])
                   * RECOG.Form_RootElement(RF, "Mj1", j, z[2 * j]);
      else
        res := res * RECOG.Form_RootElement(RF, "M1j", j, -z[2 * j - 1])
                   * RECOG.Form_RootElement(RF, "Sff", j, -z[2 * j]);
      fi;
    od;
    return res^c;
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
  N := z -> -(z * RECOG.ClassicalStandardForm(type, d, f) * z) / 2;
  Wz := function(z)
    local r;
    r := siegel1(n, z);
    return r * siegel1(n - 1, -z / N(z)) * r;
  end;
  if type = "O-" then
    w2 := e[2 * mm + 2];
    gh := Z(q^2);
    alpha := gh^((q + 1) / 2);
    t := siegel1(n, -w1);
    s := Wz(w1);
    z := (gh + gh^q) / 2 * w1 + (gh - gh^q) / (2 * alpha) * w2;
  else
    t := siegel1(n, -2 * w1);
    s := Wz(2 * w1);
    z := 2 * Z(q) * w1;
  fi;
  delta := Wz(z) * s^-1;
  return [s, t, delta, F[4], v];
end;
