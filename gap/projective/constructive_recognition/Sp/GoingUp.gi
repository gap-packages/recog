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

# Root elements of Sp(<n>,q), q = Size(<f>), as words in the standard
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
  if IsOddInt(Size(f)) then
    res.tau := [One(f), One(f) / 2];
  fi;

  if n >= 4 then
    res.conjugator[2] := res.one;
    for j in [3 .. n / 2] do
      res.conjugator[j] := res.conjugator[j - 1] * v * u;
    od;
  fi;
  return res;
end;

#############################################################################
##
##  The GoingUp for Sp(d,q), q even. GoingDown and FinalDescent lead to an
##  Omega^+(6,q) (see main.gi), and the GoingUp climbs a chain of groups
##  Omega^+(U, Q), for quadratic forms Q with polar form beta, with random
##  elements of Sp(V), which do not preserve Q. By [EHNPR], Lemma
##  GoingUpMixedForm, a step with n' = 2n-2 <= d keeps H = <Y> and H^g in
##  Omega(V, Q~) for Q~ = Q + beta(-, b)^2 and a unique b in N
##  (RECOG.Sp_MixedQuadraticForm). The adapted basis is standard for Q~ on
##  W and an arbitrary symplectic basis of its orthogonal complement, on
##  which H and H^g act trivially; so relative to it the form is again the
##  standard one of type +.
##
##  The return to Sp(V) uses a transvection. For a quadratic form Q with
##  polar form beta, g in Sp(V) with Q o g^-1 = Q + beta(-, c)^2, v
##  singular with beta(v, c) = 0, and w orthogonal to v,
##     rho^Q(v, w) rho^(Q o g^-1)(v, w) = T(v, beta(w, c)^2),
##  since in characteristic 2 rho^Q(v, w) = 1 + N_A + Q(w) N_T with
##  x N_A = beta(x, w) v + beta(x, v) w and x N_T = beta(x, v) v, whose
##  products vanish; and rho^(Q o g^-1)(v, w) = rho^Q(v g^-1, w g^-1)^g.
##  For v and w in U meet Ug both factors are words in Y and g. This
##  happens in two ways:
##   - if the chain reaches degree d, then U = V, and g is a random element
##     (RECOG.Sp_EvenAscent);
##   - otherwise in the last step, 2n-2 > d, where U meets Ug in dimension
##     2n-d >= 4; c is in general not orthogonal to that intersection, and
##     H and H^g preserve no common quadratic form (RECOG.Sp_EvenFinalStep).
##  T(v, 1) and Y give the standard generators of Sp(U)
##  (RECOG.Sp_FromOmegaAndTransvection), and in the second case the GoingUp
##  step of Sp finishes with the same g. [EHNPR] leaves this ascent open.
##
#############################################################################

# The vector c with Q o <g>^-1 = Q + beta(-, c)^2 for the standard
# quadratic form Q of type + on GF(q)^<d>, q = Size(<f>) even, and an
# isometry <g> of its polar form beta: the difference is a sum of squares
# of coordinates, with coefficients Q(b_k g^-1) - Q(b_k) = l_k^2, l = c J
# for the Gram matrix J of beta, and J^-1 = J
RECOG.Sp_EvenFormDifference := function(g, d, f)
  local gi, gA, l;

  gi := g^-1;
  gA := gi * RECOG.ClassicalStandardQuadraticForm("O+", d, f);
  l := List([1 .. d], k -> RECOG.SqrtFFE2(gA[k] * gi[k], Size(f)));
  return l * RECOG.ClassicalStandardForm("O+", d, f);
end;

# The upper triangular matrix, relative to std.bas, of the quadratic form
# Q~ = Q + beta(-, b)^2 for the candidate <g> of
# RECOG.Form_GoingUpDoublingElement, n' = 2n-2 <= d, where Q is the
# standard form of type + and c = b + b', b in N and b' in Ng, for
# c of RECOG.Sp_EvenFormDifference ([EHNPR], Lemma GoingUpMixedForm); or
# fail if c does not lie in N + Ng. Only the diagonal changes, on T.
RECOG.Sp_MixedQuadraticForm := function(std, g)
  local f, d, n, c, N, M, x, l, A, k;

  f := std.f;
  d := std.d;
  n := std.n;
  c := RECOG.Sp_EvenFormDifference(g, d, f);
  N := SemiEchelonMat(g{[1 .. n]}{[n + 1 .. d]}).vectors;
  N := List(N, r -> Concatenation(ListWithIdenticalEntries(n, Zero(f)), r));
  ConvertToMatrixRep(N, f);
  M := Concatenation(N, N * g);
  x := SolutionMat(M, c);
  if x = fail then
    return fail;
  fi;
  l := (x{[1 .. Length(N)]} * N) * RECOG.ClassicalStandardForm("O+", d, f);
  A := MutableCopyMat(RECOG.ClassicalStandardQuadraticForm("O+", d, f));
  for k in [n + 1 .. d] do
    A[k, k] := l[k]^2;
  od;
  return A;
end;

# Step 4 of the GoingUp step in the orthogonal chain of Sp(d,q), q even,
# in place of RECOG.Form_GoingUpAdaptBasis: a standard basis of N for
# Q~ = std.quad, and a symplectic standard basis of its orthogonal
# complement in T. Unbinds std.quad.
RECOG.Sp_MixedAdaptBasis := function(std, g)
  local f, d, n, T, formT, N, rest;

  f := std.f;
  d := std.d;
  n := std.n;
  T := [n + 1 .. d];
  formT := RECOG.ClassicalForm("O+", d - n, f);
  formT.quad := std.quad{T}{T};
  Unbind(std.quad);
  if 2 * n - 2 >= d then
    N := RECOG.FormStandardBasis(formT, IdentityMat(d - n, f));
  else
    N := RECOG.FormStandardBasis(formT,
             SemiEchelonMat(g{[1 .. n - 2]}{T}).vectors);
    rest := NullspaceMat(formT.gram * TransposedMat(N));
    Unbind(formT.quad);
    N := Concatenation(N, RECOG.FormStandardBasis(formT, rest));
  fi;
  return DirectSumMat(IdentityMat(n, f), N);
end;

# Vectors v and w for the transvection T(v, 1) of the head of this section,
# given the matrix <g> of an element of Sp(<d>,q), q = Size(<f>) even,
# relative to a standard basis of the form Q of type +, and the span U of
# its first <n> vectors: v, w in U meet Ug, v singular with beta(v, c) = 0
# and beta(v, w) = 0, and beta(w, c) = 1. Returns a record with components
# `v` and `w`, or fail if there are none, for example if c is orthogonal
# to U meet Ug.
RECOG.Sp_EvenTransvectionVectors := function(g, n, d, f)
  local form, cJ, X, i, w, wJ, K, S, sing;

  form := RECOG.ClassicalForm("O+", d, f);
  cJ := RECOG.Sp_EvenFormDifference(g, d, f) * form.gram;
  if n = d then
    X := IdentityMat(d, f);
  else
    X := SumIntersectionMat(IdentityMat(d, f){[1 .. n]}, g{[1 .. n]})[2];
  fi;
  i := First([1 .. Length(X)], k -> not IsZero(X[k] * cJ));
  if i = fail then
    return fail;
  fi;
  w := X[i] / (X[i] * cJ);
  wJ := w * form.gram;

  # v in the subspace S of X orthogonal to w and c
  K := NullspaceMat(TransposedMat([List(X, x -> x * wJ),
                                   List(X, x -> x * cJ)]));
  if K = [] then
    return fail;
  fi;
  S := K * X;
  sing := RECOG.FormQuadSingularVector(form, S, S * form.gram,
              List(S, x -> RECOG.FormQuadraticValue(form, x)));
  if sing = fail then
    return fail;
  fi;
  return rec( v := sing.e, w := w );
end;

# rho(v, w) in Omega^+(n,q) as a word, for the record <R> of
# RECOG.O_RootElements, a singular vector v and w orthogonal to v, given
# by their n coordinates: rho(v, w) = rho(e_1, z)^(h^-1) for h mapping v
# to e_1 and z = w h, and rho(e_1, z) is the product of the See(j, -z_(e_j))
# and Mj1(j, z_(f_j)) (see ../O/GoingUp.gi), as z_(f_1) = 0 and
# rho(e_1, e_1) = 1
RECOG.Sp_EvenSiegelWord := function(R, v, w)
  local h, z, res, j;

  h := RECOG.Form_MapToStd(R, v);
  z := w * h.mat;
  res := R.one;
  for j in [2 .. Length(v) / 2] do
    res := res * RECOG.Form_RootElement(R, "See", j, -z[2 * j - 1])
               * RECOG.Form_RootElement(R, "Mj1", j, z[2 * j]);
  od;
  return h.word * res * h.word^-1;
end;

# The standard generators of Sp(n,q), q = Size(<f>) even, as words, from
# the record <R> of root elements of Omega^+(n,q) on its standard
# generators R.Y, a word <T> for the transvection T(v, 1) and the singular
# vector <v>, by its n coordinates. With h of RECOG.Form_MapToStd mapping v
# to e_1, l = T^h = T(e_1, 1) and t = l^(s s') = T(f_1, 1), as s s' maps
# e_1 to f_1; s = l t l on (e_1, f_1); delta = (delta delta')^(q/2), as
# delta delta' = diag(gamma^2, gamma^-2) on the first pair; u = s',
# x = See(2, 1) and v are the elements of Omega^+ of these names, as
# signs do not matter.
RECOG.Sp_FromOmegaAndTransvection := function(R, T, v, f)
  local Y, l, t;

  Y := R.Y;
  l := T^RECOG.Form_MapToStd(R, v).word;
  t := l^(Y[1] * Y[4]);
  return [l * t * l, t, (Y[3] * Y[6])^(Size(f) / 2), Y[4],
          RECOG.Form_RootElement(R, "See", 2, One(f)), Y[7]];
end;

# The return to Sp(V) once the orthogonal chain has reached degree d (see
# the head of this section), for the record <std> of RECOG.Sp_EvenGoingUp,
# which then holds Omega^+(V, Q) for the standard form Q relative to
# std.bas: a random a of std.G with v and w of
# RECOG.Sp_EvenTransvectionVectors, U = V, gives T(v, 1). Replaces std.Yx
# by words for the standard generators of Sp(d,q) relative to std.bas and
# returns true, or returns fail after <N> random selections.
RECOG.Sp_EvenAscent := function(std, N)
  local f, d, F, R, a, amat, tv, ai, T, words;

  f := std.f;
  d := std.d;
  F := GeneratorsWithMemory(ListWithIdenticalEntries(8, ()));
  R := RECOG.O_RootElements(F{[1 .. 7]}, d, f);
  repeat
    if N = 0 then
      return fail;
    fi;
    N := N - 1;
    a := PseudoRandom(std.G);
    amat := std.bas * StripMemory(a) * std.basi;
    tv := RECOG.Sp_EvenTransvectionVectors(amat, d, d, f);
  until tv <> fail;

  ai := amat^-1;
  T := RECOG.Sp_EvenSiegelWord(R, tv.v, tv.w)
       * RECOG.Sp_EvenSiegelWord(R, tv.v * ai, tv.w * ai)^F[8];
  words := RECOG.Sp_FromOmegaAndTransvection(R, T, tv.v, f);
  Assert(1, ResultOfStraightLineProgram(SLPOfElms(words),
                Concatenation(RECOG.ClassicalStandardGenerators("O+", d, f).all,
                              [amat]))
            = RECOG.ClassicalStandardGenerators("Sp", d, f).all);
  std.Yx := ResultOfStraightLineProgram(SLPOfElms(words),
                Concatenation(std.Yx,
                    [ResultOfStraightLineProgram(SLPOfElm(a), std.Xf)]));
  std.type := "Sp";
  return true;
end;

# The last step of the orthogonal chain of Sp(d,q), q even, for 2n-2 > d
# (see the head of this section), for the record <std> of
# RECOG.Sp_EvenGoingUp: g~ of RECOG.Form_GoingUpDoublingElement, which
# then ignores the quadratic form of H^g, T(v, 1) for v, w in U meet Ug~,
# the standard generators of Sp(U), and those of Sp(V) by
# RECOG.Form_GoingUpNewGenerators for Sp with the same g~. Returns fail, or
# true after replacing std.Yx as RECOG.GoingUpStep does.
RECOG.Sp_EvenFinalStep := function(std, N)
  local f, d, n, R, k, dbl, tv, g, gi, F, RF, T, YSp, words, ax, tx, bx,
        gx;

  f := std.f;
  d := std.d;
  n := std.n;
  R := RECOG.GoingUpParameters("O+").rootElements(n, f);
  k := N;
  repeat
    if k = 0 then
      return fail;
    fi;
    k := k - 1;
    dbl := RECOG.Form_GoingUpDoublingElement(std, R.Y, R, N);
    if dbl = fail then
      return fail;
    fi;
    tv := RECOG.Sp_EvenTransvectionVectors(dbl.g, n, d, f);
  until tv <> fail;

  g := dbl.g;
  gi := g^-1;
  F := GeneratorsWithMemory(ListWithIdenticalEntries(8, ()));
  RF := RECOG.O_RootElements(F{[1 .. 7]}, n, f);
  T := RECOG.Sp_EvenSiegelWord(RF, tv.v{[1 .. n]}, tv.w{[1 .. n]})
       * RECOG.Sp_EvenSiegelWord(RF, (tv.v * gi){[1 .. n]},
                                 (tv.w * gi){[1 .. n]})^F[8];
  YSp := RECOG.Sp_FromOmegaAndTransvection(RF, T, tv.v{[1 .. n]}, f);
  words := RECOG.Form_GoingUpNewGenerators(
               rec( f := f, d := d, n := n, type := "Sp" ), YSp, fail, g);
  words := ResultOfStraightLineProgram(SLPOfElms(words),
                                       Concatenation(YSp, [F[8]]));
  Assert(1, ResultOfStraightLineProgram(SLPOfElms(words),
                Concatenation(List(RECOG.ClassicalStandardGenerators(
                                       "O+", n, f).all,
                                   x -> RECOG.GoingUpEmbed(x, d, f)),
                              [g]))
            = RECOG.ClassicalStandardGenerators("Sp", d, f).all);

  # g~ = (t^a)^b, as a word in the input generators
  ax := ResultOfStraightLineProgram(SLPOfElm(dbl.a), std.Xf);
  tx := ResultOfStraightLineProgram(SLPOfElm(dbl.t), std.Yx);
  bx := ResultOfStraightLineProgram(SLPOfElm(dbl.b), std.Yx);
  gx := bx^-1 * ax^-1 * tx * ax * bx;
  std.Yx := ResultOfStraightLineProgram(SLPOfElms(words),
                                        Concatenation(std.Yx, [gx]));
  std.n := d;
  std.type := "Sp";
  return true;
end;

# GoingUp for Sp(d,q), q even (see the head of this section): <G> is
# Sp(d,q) with generators with memory, and <init> describes an embedded
# Omega^+(6,q) as for RECOG.GoingUp, with init.bas a standard basis of V
# for a multiple of the form of <G> whose first six vectors are a standard
# basis for the quadratic form of that Omega^+(6,q). Returns a record as
# RECOG.GoingUp does, for the standard generators of Sp(d,q).
RECOG.Sp_EvenGoingUp := function(G, init)
  local gens, f, Xf, bas, std;

  gens := GeneratorsOfGroup(G);
  f := DefaultFieldOfMatrixGroup(G);
  Xf := GeneratorsWithMemory(ListWithIdenticalEntries(Length(gens), ()));
  bas := MutableCopyMat(init.bas);
  ConvertToMatrixRep(bas, f);
  std := rec( G := G, type := "O+", f := f, d := NrRows(gens[1]),
              n := init.n, bas := bas, basi := bas^-1, Xf := Xf,
              Yx := ResultOfStraightLineProgram(init.slp, Xf),
              mixed := true );

  while 2 * std.n - 2 <= std.d do
    Info(InfoRecog_ClassicalNatural, 2, "GoingUp: O+(", std.n, ") in Sp(",
         std.d, ")");
    repeat
    until RECOG.GoingUpStep(std, RECOG.GoingUpRandomBound) = true;
  od;
  Unbind(std.mixed);
  Info(InfoRecog_ClassicalNatural, 2, "GoingUp: O+(", std.n, ") to Sp(",
       std.d, ")");
  if std.n = std.d then
    repeat
    until RECOG.Sp_EvenAscent(std, RECOG.GoingUpRandomBound) = true;
  else
    repeat
    until RECOG.Sp_EvenFinalStep(std, RECOG.GoingUpRandomBound) = true;
  fi;
  return rec( slp := SLPOfElms(std.Yx), bas := std.bas );
end;
