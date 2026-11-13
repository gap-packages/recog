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
##  The root elements of symplectic groups for the GoingUp of [EHNPR]
##  (see ../GoingUp.gi), Section 'GoingUp algorithm', whose other parts are
##  shared with special unitary groups.
##
#############################################################################

# Root elements of Sp(<n>,q), q = Size(<f>) odd, as words in the standard
# generators, in the record described in ../GoingUp.gi. <Y> are elements
# with memory standing for the standard generators of Sp(n,q) relative to
# the standard basis, in the order of RECOG.ClassicalStandardGenerators;
# only their words are used, so they may be generators with memory of any
# group.
# Conjugating Lf(gamma^0) = t by powers of delta gives Lf(gamma^(2k)), and
# conjugating See(2, gamma^0) = x gives See(2, gamma^k), gamma = Z(q).
# The powers gamma^(2k) and gamma^k, 0 <= k < [GF(q):GF(p)], are bases of
# GF(q) over GF(p). The other root elements on the first two pairs are
# conjugates by s on one or both of them, and (v u)^(j-2) fixes the first
# pair and maps the second pair to the j-th.
RECOG.Sp_RootElements := function(Y, n, f)
  local s, t, delta, u, x, v, ext, gamma, s2, see, long, short, res, j;

  s := Y[1];
  t := Y[2];
  delta := Y[3];
  u := Y[4];
  x := Y[5];
  v := Y[6];
  ext := DegreeOverPrimeField(f);
  gamma := Z(Size(f));
  s2 := s^u;
  see := List([0 .. ext - 1], k -> x^(delta^k));
  long := Basis(f, List([0 .. ext - 1], k -> gamma^(2 * k)));
  short := Basis(f, List([0 .. ext - 1], k -> gamma^k));

  res := rec(
    f := f,
    Y := Y,
    one := s^0,
    s := s,
    t := t,
    u := u,
    v := v,
    eps := -One(f),
    conj := c -> c,
    longUnit := One(f),
    torus := delta,
    torusDiag := [gamma, gamma^-1],
    gamma := gamma,
    tau := [One(f), One(f) / 2],
    Lf := List([0 .. ext - 1], k -> t^(delta^-k)),
    See := see,
    Sff := List(see, y -> (y^-1)^(s * s2)),
    M1j := List(see, y -> (y^-1)^s),
    Mj1 := List(see, y -> (y^-1)^s2),
    bases := rec( Lf := long, Le := long, See := short, Sff := short,
                  M1j := short, Mj1 := short ),
    conjugator := [],
    powers := rec( Lf := [], Le := [], See := [], Sff := [], M1j := [],
                   Mj1 := [] ),
  );
  res.Le := List(res.Lf, y -> y^s);

  if n >= 4 then
    res.conjugator[2] := res.one;
    for j in [3 .. n / 2] do
      res.conjugator[j] := res.conjugator[j - 1] * v * u;
    od;
  fi;
  return res;
end;
