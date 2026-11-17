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
##  The root elements of special unitary groups of odd degree for the
##  rewriting of ../Rewrite.gi.
##
#############################################################################

# Root elements of SU(<d>,q0), d >= 5 odd, q = q0^2 = Size(<f>) odd, for
# RECOG.Form_Rewrite, on the standard generators <Y> with memory: those of
# RECOG.SU_RootElements for the SU(2m) on the m hyperbolic pairs, and the
# component `aniso` (see ../GoingUp.gi) for w_1. That SU(2m) has the
# standard generators s, t, delta, u, v of SU(d) and, with s2 = s^u,
#   x+ = ([x, x^u]^(s2^-1))^(y^k),  y+ = y (y^-1)^u,
# where [x, x^u] = Sff(2, -1), its conjugate by s2^-1 is M1j(2, -1/alpha),
# and gamma^-k = -alpha. The assertion checks these words.
# Fw and Ew are the unitary Siegel transformations rho(f_1, z, lam) and
# rho(e_1, z, lam) of ../SU/GoingUp.gi with z in <w_1>: the conjugates of
# x = rho(f_1, -w_1, -1/2) by the y^-i, whose parameters z span <w_1> over
# GF(p), and their conjugates by s. Their products are not rho(., z, lam)
# for a lam fixed by z; aniso.lambda(kind, z) returns the lam of the word
# for z, by rho(p, z, lam) rho(p, z', lam') = rho(p, z + z', lam + lam' -
# beta(z, z')).
RECOG.SU_RewriteRootElements := function(Y, d, f)
  local std, q, q0, p, gamma, alpha, m, s2, k, xp, yp, P, R, ext, ts, lam,
        zF, zE, lambda;

  std := RECOG.ClassicalStandardGenerators("SU", d, f);
  q := Size(f);
  q0 := RootInt(q, 2);
  p := Characteristic(f);
  gamma := Z(q);
  alpha := gamma^((q0 + 1) / 2);
  m := QuoInt(d, 2);

  # Y = s, t, delta, u, v, x, y
  s2 := Y[1]^Y[4];
  k := (q - 1 - LogFFE(-alpha, gamma)) mod (q - 1);
  xp := (Comm(Y[6], Y[6]^Y[4])^(s2^-1))^(Y[7]^k);
  yp := Y[7] * (Y[7]^-1)^Y[4];
  P := [Y[1], Y[2], Y[3], Y[4], Y[5], xp, yp];
  R := RECOG.SU_RootElements(P, 2 * m, f);
  Assert(1, ResultOfStraightLineProgram(SLPOfElms(P), std.all)
            = List(RECOG.ClassicalStandardGenerators("SU", 2 * m, f).all,
                   x -> RECOG.GoingUpEmbed(x, d, f)));

  # rho(f_1, z, lam) maps e_1 to e_1 - z + lam f_1, rho(e_1, z, lam) maps
  # f_1 to f_1 - z + lam e_1
  ext := DegreeOverPrimeField(f);
  ts := List([0 .. ext - 1], i -> std.x^(std.y^-i));
  zF := List(ts, x -> -x[1, d]);
  zE := List(ts, x -> -(x^std.s)[2, d]);
  lam := rec( Fw := List(ts, x -> x[1, 2]),
              Ew := List(ts, x -> (x^std.s)[2, 1]) );
  R.Fw := List([0 .. ext - 1], i -> Y[6]^(Y[7]^-i));
  R.Ew := List(R.Fw, x -> x^Y[1]);
  R.bases.Fw := Basis(VectorSpace(GF(p), zF), zF);
  R.bases.Ew := Basis(VectorSpace(GF(p), zE), zE);
  Assert(1, R.bases.Fw <> fail and R.bases.Ew <> fail);
  R.powers.Fw := [];
  R.powers.Ew := [];

  # the word of RECOG.GoingUpRootWord for z is the product of the c_k-th
  # powers of the words for the basis vectors b_k, k ascending, and
  # rho(p, b, l)^c = rho(p, c b, c l - c(c-1)/2 b^(q0+1))
  lambda := function(kind, z)
    local B, c, res, i, j;
    B := BasisVectors(R.bases.(kind));
    c := List(Coefficients(R.bases.(kind), z[1]), IntFFE);
    res := Zero(f);
    for i in [1 .. Length(B)] do
      res := res + c[i] * lam.(kind)[i]
             - c[i] * (c[i] - 1) / 2 * B[i]^(q0 + 1);
      for j in [i + 1 .. Length(B)] do
        res := res - c[i] * c[j] * B[i] * B[j]^q0;
      od;
    od;
    return res;
  end;
  R.aniso := rec( pos := [d], pairs := m, gram := [[One(f)]],
                  unit := [One(f)], toField := z -> z[1], lambda := lambda );
  return R;
end;
