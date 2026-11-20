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
##  shared with symplectic groups.
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
