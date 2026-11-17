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
##  The root elements of special unitary groups for the GoingUp of [EHNPR]
##  (see ../GoingUp.gi), Section 'GoingUp algorithm', whose other parts are
##  shared with symplectic groups, and the standard generators of odd
##  degree in its last step.
##
#############################################################################

# Root elements of SU(<n>,q0), q = q0^2 = Size(<f>) odd, as words in the
# standard generators, in the record described in ../GoingUp.gi. <Y> are
# as for RECOG.Sp_RootElements.
# With gamma = Z(q), alpha = gamma^((q0+1)/2) and gamma0 = gamma^(q0+1) =
# alpha^2: conjugating Lf(alpha) = t by delta^-k gives
# Lf(alpha gamma0^(2k)), and conjugating M1j(2, 1) = x by y^-k gives
# M1j(2, gamma^(2k)). The gamma^(2k), 0 <= k < [GF(q):GF(p)], are a basis
# of GF(q) over GF(p), and the alpha gamma0^(2k), 0 <= k < [GF(q0):GF(p)],
# one of the parameters of Lf, the elements of trace 0. Conjugation by s
# maps Lf(lambda) to Le(-lambda/gamma0) and M1j(2, lambda) to
# See(2, lambda/alpha); conjugation by s2 = s^u maps M1j(2, lambda) to
# Sff(2, alpha lambda), and conjugation by s s2 to Mj1(2, -lambda^q0). As
# for Sp, (v u)^(j-2) fixes the first pair and maps the second to the j-th.
RECOG.SU_RootElements := function(Y, n, f)
  local s, t, delta, u, v, x, y, q0, ext, gamma, alpha, gamma0, s2, m1j,
        short, trace0, res, j;

  s := Y[1];
  t := Y[2];
  delta := Y[3];
  u := Y[4];
  v := Y[5];
  x := Y[6];
  y := Y[7];
  q0 := RootInt(Size(f), 2);
  ext := DegreeOverPrimeField(f);
  gamma := Z(Size(f));
  alpha := gamma^((q0 + 1) / 2);
  gamma0 := alpha^2;
  s2 := s^u;
  m1j := List([0 .. ext - 1], k -> x^(y^-k));
  short := List([0 .. ext - 1], k -> gamma^(2 * k));
  trace0 := List([0 .. ext / 2 - 1], k -> alpha * gamma0^(2 * k));

  res := rec(
    f := f,
    Y := Y,
    one := s^0,
    s := s,
    t := t,
    u := u,
    v := v,
    eps := One(f),
    conj := c -> c^q0,
    longUnit := alpha,
    torus := y,
    torusDiag := [gamma, gamma^-q0, gamma^-1, gamma^q0],
    gamma := gamma,
    tau := [alpha, -1 / (2 * alpha)],
    Lf := List([0 .. ext / 2 - 1], k -> t^(delta^-k)),
    M1j := m1j,
    See := List(m1j, w -> w^s),
    Sff := List(m1j, w -> w^s2),
    Mj1 := List(m1j, w -> w^(s * s2)),
    bases := rec(
      Lf := Basis(VectorSpace(PrimeField(f), trace0), trace0),
      Le := Basis(VectorSpace(PrimeField(f), -trace0 / gamma0),
                  -trace0 / gamma0),
      M1j := Basis(f, short),
      See := Basis(f, short / alpha),
      Sff := Basis(f, alpha * short),
      Mj1 := Basis(f, List(short, c -> -c^q0)) ),
    conjugator := [],
    powers := rec( Lf := [], Le := [], See := [], Sff := [], M1j := [],
                   Mj1 := [] ),
  );
  res.Le := List(res.Lf, w -> w^s);

  if n >= 4 then
    res.conjugator[2] := res.one;
    for j in [3 .. n / 2] do
      res.conjugator[j] := res.conjugator[j - 1] * v * u;
    od;
  fi;
  return res;
end;

# Step 5 of the GoingUp step for SU ([EHNPR], 'Constructing the enlarged
# group'): the standard generators of SU(W), W = U + N, as words in the
# standard generators <Y> of SU(U) and g~, whose matrix relative to the
# adapted basis is <g>, as in RECOG.Form_GoingUpNewGenerators. If n' = d
# is odd, W = V and x, y are those of odd degree, on <e_1, f_1, w_1>.
#
# They are words in the unitary Siegel transformations
#   rho(p, z, lam): x -> x + beta(x, z) p - beta(x, p) z + lam beta(x, p) p
# for isotropic p, z orthogonal to p and lam + lam^q0 = -beta(z, z), which
# satisfy rho(p, z, lam) rho(p, z', lam') = rho(p, z + z', lam + lam' -
# beta(z, z')) and rho(p, z, lam)^h = rho(ph, zh, lam) for isometries h:
#   x = rho(f_1, -w_1, -1/2),
#   y = rho(f_1, a w_1, A) rho(e_1, -(a/A) w_1, A^-q0)
#       rho(f_1, a A^(q0-1) w_1, A) s^-1
# with A = alpha gamma and a of norm a^(q0+1) = -(A + A^q0); the product of
# the three is monomial, e_1 -> A f_1, f_1 -> A^-q0 e_1 and
# w_1 -> -A^(q0-1) w_1. [EHNPR] leaves these factorisations open ('The
# standard generators of CL(W)', part (3)).
# As for Omega (see ../O/GoingUp.gi), rho(p, z, lam) with p = e_m or f_m in
# the pivot space P and z = a_1 + a_2 g~ in A + N, a_i in A, is
# rho(p, a_1, lam_1) rho(p, a_2, lam_2)^g~, as g~ fixes p; with
# c = v^(m-1), rho(p, a, lam) = rho(p c^-1, a c^-1, lam)^c, a product of
# root elements of SU(U) on the first pair: with z = sum of
# zeta_j e_j + xi_j f_j, j >= 2, rho(f_1, z, lam) is the product of the
# M1j(j, -zeta_j) Sff(j, -xi_j) and Lf(lam + sum zeta_j xi_j^q0), and
# rho(e_1, z, lam) that of the See(j, -zeta_j) Mj1(j, xi_j^q0) and
# Le(lam + sum zeta_j xi_j^q0). Since c fixes N, rho(e_1, z, lam) and
# rho(f_1, z, lam) for z in N are rho(e_m, z, lam)^(c^-1) and
# rho(f_m, z, lam)^(c^-1).
RECOG.SU_GoingUpNewGenerators := function(std, Y, R, g)
  local f, q0, d, n, m, F, res, gt, RF, form, beta, cmat, c, solver,
        siegelU, siegelP, siegel1, gamma, alpha, A, a, w1, x, y;

  f := std.f;
  d := std.d;
  n := std.n;
  F := GeneratorsWithMemory(ListWithIdenticalEntries(Length(Y) + 1, ()));
  res := RECOG.Form_GoingUpNewGenerators(std, Y, R, g, F);
  if Minimum(2 * n - 2, d) < d or IsEvenInt(d) then
    return res;
  fi;

  q0 := RootInt(Size(f), 2);
  m := n / 2;
  gt := F[Length(F)];
  RF := RECOG.SU_RootElements(F{[1 .. Length(Y)]}, n, f);
  form := RECOG.ClassicalForm("SU", d, f);
  beta := {x, y} -> RECOG.FormValue(form, x, y);

  # c = v^(m-1) maps the first pair to the m-th; cmat is c^-1 on U
  c := RF.v^(m - 1);
  cmat := (RECOG.ClassicalStandardGenerators("SU", n, f).v)^(1 - m);

  # a_2 in A, as coordinates on its first n-2 basis vectors, with the same
  # projection to N as a vector x of A + N
  solver := RECOG.GoingUpSolver(g{[1 .. n - 2]}{[n + 1 .. d]});

  # rho(p, a, lam) for p = e_m (pos = n-1) or f_m (pos = n) and a in A,
  # given by its first n-2 coordinates
  siegelU := function(pos, a, lam)
    local z, res, corr, j;
    z := Concatenation(a, [Zero(f), Zero(f)]) * cmat;
    res := RF.one;
    corr := lam;
    for j in [2 .. m] do
      corr := corr + z[2 * j - 1] * z[2 * j]^q0;
      if pos = n - 1 then
        res := res * RECOG.Form_RootElement(RF, "See", j, -z[2 * j - 1])
                   * RECOG.Form_RootElement(RF, "Mj1", j, z[2 * j]^q0);
      else
        res := res * RECOG.Form_RootElement(RF, "M1j", j, -z[2 * j - 1])
                   * RECOG.Form_RootElement(RF, "Sff", j, -z[2 * j]);
      fi;
    od;
    if pos = n - 1 then
      res := res * RECOG.Form_RootElement(RF, "Le", 1, corr);
    else
      res := res * RECOG.Form_RootElement(RF, "Lf", 1, corr);
    fi;
    return res^c;
  end;

  # rho(p, x, lam) for p as for siegelU and x in A + N, given by its d
  # coordinates
  siegelP := function(pos, x, lam)
    local a2, a2g, a1, lam1, lam2;
    a2 := solver(x{[n + 1 .. d]});
    a2g := Concatenation(a2, Zero(x{[n - 1 .. d]})) * g;
    a1 := Concatenation(x{[1 .. n - 2]} - a2g{[1 .. n - 2]},
                        Zero(x{[n - 1 .. d]}));
    lam1 := -beta(a1, a1) / 2;
    lam2 := lam - lam1 + beta(a1, a2g);
    return siegelU(pos, a1{[1 .. n - 2]}, lam1)
           * siegelU(pos, a2, lam2)^gt;
  end;

  # rho(e_1, x, lam) (pos = n-1) or rho(f_1, x, lam) (pos = n) for x in N
  siegel1 := {pos, x, lam} -> siegelP(pos, x, lam)^(c^-1);

  gamma := Z(Size(f));
  alpha := gamma^((q0 + 1) / 2);
  A := alpha * gamma;
  a := RootFFE(f, -(A + A^q0), q0 + 1);
  w1 := IdentityMat(d, f)[d];
  x := siegel1(n, -w1, -One(f) / 2);
  y := siegel1(n, a * w1, A) * siegel1(n - 1, -(a / A) * w1, A^-q0)
       * siegel1(n, a * A^(q0 - 1) * w1, A) * F[1]^-1;
  res := ShallowCopy(res);
  res[6] := x;
  res[7] := y;
  return res;
end;
