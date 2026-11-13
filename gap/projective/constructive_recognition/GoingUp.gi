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
##  GoingUp for classical groups in their natural representation, as in
##  [EHNPR] (see GoingDown.gi), Section 'GoingUp algorithm', for SL and for
##  Sp in odd characteristic.
##
##  A GoingUp step ([EHNPR], 'The GoingUpStep algorithm', whose steps are
##  numbered as here) starts from a stingray embedding: a basis B of
##  V = GF(q)^d, a standard basis for Sp, whose first n vectors span U, and
##  words for the standard generators Y of CL(U) relative to these vectors,
##  extended by the identity on T = <v_(n+1), ..., v_d>. With the overlap
##  k = 1 for SL and 2 for Sp, it constructs the same for degree
##  n' = min(2n - k, d), keeping the first n vectors of B:
##
##     U = A + P, P = <v_(n-k+1), ..., v_n> the pivot space
##     1. t in <Y> whose fixed space on U has dimension k (the seed)
##     2. g = t^a for random a, until W = U + Ug has dimension n', T meets
##        Fix(g) in a complement of W (for Sp: W is non-degenerate), and
##        U meets Fix(g) in a suitable k-space P'
##     3. g~ = g^b with b in <Y> mapping P' onto P, so that g~ fixes P
##     4. v_(n+1), ..., v_d := a basis of N, the projection of A g~ to T,
##        and fixed vectors of g~ in T (for Sp: standard bases of N and of
##        its orthogonal complement in T); so W = U + N
##     5. the standard generators of CL(W) as words in Y and g~
##
#############################################################################

# Random selections a GoingUp step may make before it returns fail
RECOG.GoingUpRandomBound := 100;

# The functions of the GoingUp step for the classical type <type>, and its
# overlap k (see the top of this file). rootElements(n, f) returns the
# record of root elements of CL(n,q), whose component Y holds the words
# standing for the standard generators; for Sp, rootElementsOf(Y, n, f)
# returns it for given words Y. The other functions are documented where
# they are defined, in SL/GoingUp.gi and below.
RECOG.GoingUpParameters := function(type)
  local of, k;

  if type = "SL" then
    return rec( overlap := 1,
                rootElements := {n, f} -> RECOG.SL_RootElements(
                    GeneratorsWithMemory(ListWithIdenticalEntries(5, ())),
                    n, f),
                doublingElement := RECOG.SL_GoingUpDoublingElement,
                adaptBasis := RECOG.SL_GoingUpAdaptBasis,
                newGenerators := RECOG.SL_GoingUpNewGenerators );
  fi;
  if type = "Sp" then
    of := RECOG.Sp_RootElements;
  else
    ErrorNoReturn("RECOG.GoingUpParameters: unsupported type ", type);
  fi;
  k := Length(RECOG.ClassicalStandardGeneratorNames(type));
  return rec( overlap := 2,
              rootElementsOf := of,
              rootElements := {n, f} -> of(
                  GeneratorsWithMemory(ListWithIdenticalEntries(k, ())), n, f),
              doublingElement := RECOG.Form_GoingUpDoublingElement,
              adaptBasis := RECOG.Form_GoingUpAdaptBasis,
              newGenerators := RECOG.Form_GoingUpNewGenerators );
end;

# The matrix acting as <M> on the first rows of the d x d identity and
# fixing the others
RECOG.GoingUpEmbed := function(M, d, f)
  local res;
  res := IdentityMat(d, f);
  res{[1 .. NrRows(M)]}{[1 .. NrRows(M)]} := M;
  ConvertToMatrixRep(res, f);
  return res;
end;

# <powers>[1]^<c> for an integer c > 0, kept as powers[c], so that the
# SLP of a word with memory computes each power once
RECOG.GoingUpPower := function(powers, c)
  if not IsBound(powers[c]) then
    powers[c] := powers[1]^c;
  fi;
  return powers[c];
end;

# The root element for <lambda> in GF(q), as the product of the
# words[k]^c_k for the coefficients c_k of lambda in <basis>, a basis of
# GF(q) over GF(p), where words[k] = <powers>[k][1] is the root element for
# basis[k]; powers[k] is a list for RECOG.GoingUpPower. Root elements in
# one root group are additive in lambda. Factors with c_k = 0 are left
# out, and <one> stands for lambda = 0.
RECOG.GoingUpRootWord := function(powers, basis, lambda, one)
  local coeffs, res, k, y;

  coeffs := List(Coefficients(basis, lambda), IntFFE);
  res := fail;
  for k in [1 .. Length(coeffs)] do
    if coeffs[k] = 0 then
      continue;
    fi;
    y := RECOG.GoingUpPower(powers[k], coeffs[k]);
    if res = fail then
      res := y;
    else
      res := res * y;
    fi;
  od;
  if res = fail then
    return one;
  fi;
  return res;
end;

# A function mapping a vector w in the row space of <M> to a vector c with
# c * M = w, echelonising M once
RECOG.GoingUpSolver := function(M)
  local T;
  T := SemiEchelonMatTransformation(M);
  return function(w)
    local c, col, k;
    w := ShallowCopy(w);
    c := ListWithIdenticalEntries(Length(T.vectors), Zero(w[1]));
    for col in [1 .. Length(w)] do
      k := T.heads[col];
      if k > 0 and not IsZero(w[col]) then
        c[k] := w[col];
        w := w - w[col] * T.vectors[k];
      fi;
    od;
    Assert(1, IsZero(w));
    return c * T.coeffs;
  end;
end;

# One GoingUp step for the record <std> of RECOG.GoingUp, with at most <N>
# random selections. Returns fail, or true after replacing std.n, std.bas,
# std.basi and std.Yx by those of degree n'.
# As in [EHNPR], 'Bookkeeping in a matrix implementation', a is a word in
# the generators of std.G, t and b are words in Y, and the new generators
# are words in Y and g~. All but a are elements with memory of the
# trivial group (), so composing them multiplies no matrices; their
# matrices relative to std.bas are computed alongside. GAP builds SLPs
# from them, not the MSLPs of [EHNPR].
RECOG.GoingUpStep := function(std, N)
  local f, d, n, params, Y, R, dbl, C, Ci, g, words, ax, tx, bx, gx;

  f := std.f;
  d := std.d;
  n := std.n;
  params := RECOG.GoingUpParameters(std.type);

  R := params.rootElements(n, f);
  Y := R.Y;

  dbl := params.doublingElement(std, Y, R, N);
  if dbl = fail then
    return fail;
  fi;
  C := params.adaptBasis(std, dbl.g);
  ConvertToMatrixRep(C, f);
  Ci := C^-1;
  g := C * dbl.g * Ci;
  words := params.newGenerators(std, Y, R, g);

  # g~ = (t^a)^b, as a word in the input generators
  ax := ResultOfStraightLineProgram(SLPOfElm(dbl.a), std.Xf);
  tx := ResultOfStraightLineProgram(SLPOfElm(dbl.t), std.Yx);
  bx := ResultOfStraightLineProgram(SLPOfElm(dbl.b), std.Yx);
  gx := bx^-1 * ax^-1 * tx * ax * bx;

  std.Yx := ResultOfStraightLineProgram(SLPOfElms(words),
                                        Concatenation(std.Yx, [gx]));
  std.n := Minimum(2 * n - params.overlap, d);
  std.bas := C * std.bas;
  std.basi := std.basi * Ci;
  return true;
end;

# GoingUp of [EHNPR] ('Outline of the algorithm', subsection 'GoingUp
# algorithm') for the type <type>, "SL" or "Sp" (q odd): <G> is
# SL(d,q), resp. Sp(d,q) for some alternating form, with generators with
# memory, and <init> describes an embedded CL(n,q) as follows:
#  - `slp`: SLP in the generators of <G> for the standard generators of
#    CL(n,q), as in RECOG.ClassicalStandardGenerators, relative to bas
#  - `bas`: a d x d matrix whose last d-n rows are fixed by that CL(n,q);
#    for Sp, its rows are a standard basis of V for a multiple of the form
#    of <G>
#  - `n`: the degree n, at least 2 for SL and 4 for Sp
# Returns a record with the following components:
#  - `slp`: SLP in the generators of <G> for the standard generators of
#    CL(d,q) relative to bas
#  - `bas`: a basis of V, as a matrix, starting with init.bas{[1..n]}
# The rows of a basis matrix are the basis vectors, so it is the inverse
# of the matrix L of [EHNPR]. A step that fails is repeated, as it leaves
# its input unchanged; [EHNPR] returns fail instead ('Algorithmic
# conventions').
RECOG.GoingUp := function(G, type, init)
  local gens, f, Xf, bas, std;

  gens := GeneratorsOfGroup(G);
  f := DefaultFieldOfMatrixGroup(G);
  Xf := GeneratorsWithMemory(ListWithIdenticalEntries(Length(gens), ()));
  # products of matrices in plain lists are up to 15 times slower
  bas := MutableCopyMat(init.bas);
  ConvertToMatrixRep(bas, f);
  std := rec( G := G, type := type, f := f, d := NrRows(gens[1]),
              n := init.n, bas := bas, basi := bas^-1, Xf := Xf,
              Yx := ResultOfStraightLineProgram(init.slp, Xf) );

  while std.n < std.d do
    Info(InfoRecog_ClassicalNatural, 2, "GoingUp: ", type, "(", std.n,
         ") in ", type, "(", std.d, ")");
    repeat
    until RECOG.GoingUpStep(std, RECOG.GoingUpRandomBound) = true;
  od;
  return rec( slp := SLPOfElms(std.Yx), bas := std.bas );
end;

#############################################################################
##
##  The GoingUp step for the types with a form, Sp and SU, q odd.
##
##  Vectors are rows of coordinates relative to a standard basis
##  (e_1, f_1, ..., e_m, f_m), so e_i and f_i have the indices 2i-1 and 2i.
##  beta is the form of RECOG.ClassicalForm, beta(x, y) = x J y^sigma, with
##  sigma the identity for Sp and the involution c -> c^q0 of GF(q0^2) for
##  SU, and eps = beta(f_i, e_i) is -1 for Sp and 1 for SU. For isotropic
##  w, T(w, lambda) denotes the transvection
##  x -> x + lambda * beta(x, w) * w, an isometry if
##  lambda^sigma = -eps * lambda, that is, for SU if lambda has trace 0.
##
##  [EHNPR] obtains words in Y for elements of CL(U), such as b in Step 3
##  and the conjugators and transvections in 'Constructing the enlarged
##  group', by constructive membership testing (Costi, PhD thesis, Queen
##  Mary, University of London, 2009). Here they are products of the root
##  elements of RECOG.Sp_RootElements and of a torus element, found by
##  elimination, which yields each word together with its matrix.
##
##  The record R of root elements of CL(n,q), as words in standard
##  generators Y, has the following components:
##   - `f`, `Y`, `one`, and `s`, `t`, `u`, `v`: the field, Y, the identity
##     and the standard generators of these names
##   - `eps` and `conj`: eps and sigma
##   - `longUnit`: a nonzero parameter of T(e_1, .)
##   - `torus`: an element acting as diag(torusDiag) on the first basis
##     vectors and fixing the others, and `gamma`: torusDiag[1], a
##     primitive element of GF(q)
##   - `tau`: the parameters [x, y] of the factors T(a, x) and T(b, y) of
##     tau_j in RECOG.Form_GoingUpNewGenerators
##   - for each kind of root element below, the component of that name, the
##     root elements kind(2, lambda) for lambda in the GF(p)-basis
##     bases.(kind) of their parameters
##   - `conjugator`: conjugator[j] maps e_2 to e_j and f_2 to f_j, and fixes
##     e_1, f_1, and `powers`: a cache for RECOG.Form_RootElement
##  The root elements, for 2 <= j <= m = n/2, are
##   - Lf(lambda) = T(f_1, lambda): e_1 -> e_1 + lambda f_1;
##   - Le(lambda) = T(e_1, lambda): f_1 -> f_1 + eps lambda e_1;
##   - See(j, lambda): f_1 -> f_1 + lambda e_j,
##     f_j -> f_j - eps lambda^sigma e_1;
##   - Sff(j, lambda): e_1 -> e_1 + lambda f_j,
##     e_j -> e_j - eps lambda^sigma f_1;
##   - M1j(j, lambda): e_1 -> e_1 + lambda e_j,
##     f_j -> f_j - lambda^sigma f_1;
##   - Mj1(j, lambda): e_j -> e_j + lambda e_1,
##     f_1 -> f_1 - lambda^sigma f_j.
##
#############################################################################

# The root element <kind>(<j>, <lambda>) of <R>, as a word in R.Y, where
# <kind> is one of "Lf", "Le", "See", "Sff", "M1j", "Mj1", and <j> is
# ignored for "Lf" and "Le". R.powers.(kind)[j] keeps the powers of the
# conjugates of R.(kind) by R.conjugator[j] for RECOG.GoingUpRootWord,
# with j = 2 for "Lf" and "Le".
RECOG.Form_RootElement := function(R, kind, j, lambda)
  local powers;

  if kind in ["Lf", "Le"] then
    j := 2;
  fi;
  powers := R.powers.(kind);
  if not IsBound(powers[j]) then
    if j = 2 then
      powers[j] := List(R.(kind), y -> [y]);
    else
      powers[j] := List(R.(kind), y -> [y^R.conjugator[j]]);
    fi;
  fi;
  return RECOG.GoingUpRootWord(powers[j], R.bases.(kind), lambda, R.one);
end;

# The matrix of the root element <kind>(<j>, <lambda>) of <R> is the
# identity plus the entries c at the positions [i, k] of the triples
# [i, k, c] returned here. No k is also an i, so the entries act
# independently.
RECOG.Form_RootElementEntries := function(R, kind, j, lambda)
  local c;

  c := R.conj(lambda);
  if kind = "Lf" then
    return [[1, 2, lambda]];
  elif kind = "Le" then
    return [[2, 1, R.eps * lambda]];
  elif kind = "See" then
    return [[2, 2 * j - 1, lambda], [2 * j, 1, -R.eps * c]];
  elif kind = "Sff" then
    return [[1, 2 * j, lambda], [2 * j - 1, 2, -R.eps * c]];
  elif kind = "M1j" then
    return [[1, 2 * j - 1, lambda], [2 * j, 2, -c]];
  fi;
  return [[2 * j - 1, 1, lambda], [2, 2 * j, -c]];
end;

# A record for a product b of root elements and powers of the torus
# element of <R>, built by elimination on the vector <y> of length n:
# `word` is b as a word in R.Y, `y` is y b, `MT` is the transpose of the
# matrix of b, `apply(kind, j, lambda)` multiplies b by the root element
# kind(j, lambda), and `scale(k)` by R.torus^k
RECOG.Form_Elimination := function(R, y)
  local res;

  res := rec( word := R.one, y := ShallowCopy(y),
              MT := MutableCopyMat(IdentityMat(Length(y), R.f)) );
  ConvertToMatrixRep(res.MT, R.f);
  res.apply := function(kind, j, lambda)
    local x;
    res.word := res.word * RECOG.Form_RootElement(R, kind, j, lambda);
    # y r adds c y_i to y_k, and r^T M^T adds c times row i to row k
    for x in RECOG.Form_RootElementEntries(R, kind, j, lambda) do
      res.y[x[2]] := res.y[x[2]] + x[3] * res.y[x[1]];
      AddRowVector(res.MT[x[2]], res.MT[x[1]], x[3]);
    od;
  end;
  res.scale := function(k)
    local i, c;
    res.word := res.word * R.torus^k;
    for i in [1 .. Length(R.torusDiag)] do
      c := R.torusDiag[i]^k;
      res.y[i] := c * res.y[i];
      res.MT[i] := c * res.MT[i];
    od;
  end;
  return res;
end;

# An element b of CL(n,q) which maps the nonzero vector <y> to
# e_1 + (nu/2) f_1, nu = beta(y, y), that is, to e_1 if y is isotropic. It
# clears the coordinates of y one by one with root elements, as in
# Gaussian elimination, and scales the e_1-coordinate to 1 by the torus.
# Returns a record with the following components:
#  - `word`: b, as a word in R.Y
#  - `mat`: the matrix of b
RECOG.Form_MapToStd := function(R, y)
  local n, elim, apply, j, nu;

  n := Length(y);
  elim := RECOG.Form_Elimination(R, y);
  apply := elim.apply;
  y := elim.y;

  # make the e_1-coordinate nonzero
  if IsZero(y[1]) then
    if not IsZero(y[2]) then
      apply("Le", 1, R.longUnit);
    else
      j := PositionNonZero(y);
      if IsOddInt(j) then
        apply("Mj1", (j + 1) / 2, One(R.f));
      else
        apply("See", j / 2, One(R.f));
      fi;
    fi;
  fi;

  # clear the other pairs, then make the e_1-coordinate 1
  for j in [2 .. n / 2] do
    if not IsZero(y[2 * j - 1]) then
      apply("M1j", j, -y[2 * j - 1] / y[1]);
    fi;
    if not IsZero(y[2 * j]) then
      apply("Sff", j, -y[2 * j] / y[1]);
    fi;
  od;
  if not IsOne(y[1]) then
    elim.scale(LogFFE(y[1]^-1, R.gamma));
  fi;

  # y = e_1 + c f_1 has the norm nu = c^sigma + eps c, and nu/2 - c is a
  # parameter of Lf
  nu := R.conj(y[2]) + R.eps * y[2];
  if y[2] <> nu / 2 then
    apply("Lf", 1, nu / 2 - y[2]);
  fi;

  Assert(1, y = IdentityMat(n, R.f)[1] + nu / 2 * IdentityMat(n, R.f)[2]);
  return rec( word := elim.word, mat := TransposedMat(elim.MT) );
end;

# An element b of CL(n,q) which fixes e_1 and maps the isotropic vector
# <y> to f_1, where beta(e_1, y) = 1, as a record like that of
# RECOG.Form_MapToStd
RECOG.Form_MapToF1FixingE1 := function(R, y)
  local n, elim, apply, j;

  n := Length(y);
  if not IsOne(y[2]) then
    ErrorNoReturn("RECOG.Form_MapToF1FixingE1: beta(e_1, <y>) must be 1");
  fi;
  elim := RECOG.Form_Elimination(R, y);
  apply := elim.apply;
  y := elim.y;

  # these root elements fix e_1 and add multiples of the f_1-coordinate;
  # the last one clears the e_1-coordinate, as y is isotropic
  for j in [2 .. n / 2] do
    if not IsZero(y[2 * j - 1]) then
      apply("See", j, -y[2 * j - 1]);
    fi;
    if not IsZero(y[2 * j]) then
      apply("Mj1", j, R.conj(y[2 * j]));
    fi;
  od;
  if not IsZero(y[1]) then
    apply("Le", 1, -R.eps * y[1]);
  fi;

  Assert(1, y = IdentityMat(n, R.f)[2]);
  return rec( word := elim.word, mat := TransposedMat(elim.MT) );
end;

# The seed t of the GoingUp step ([EHNPR], Step 1 (Constructing the seed
# element)): an element of CL(n,q), q a power of <p>, whose fixed space is
# a non-degenerate plane, given as a word in the components s, t, u, v of
# <Y>, which may be words or matrices.
# The pair cycle v fixes <e_1 + ... + e_m, f_1 + ... + f_m>, on which beta
# takes the value m = n/2; if p divides m, then s t^-1 v u fixes the plane
# <e_2 + ... + e_m, f_2 + ... + f_m> instead, where beta is m - 1.
RECOG.Form_GoingUpSeed := function(Y, n, p)
  if (n / 2) mod p <> 0 then
    return Y.v;
  fi;
  return Y.s * Y.t^-1 * Y.v * Y.u;
end;

# Steps 1 to 3 of the GoingUp step of [EHNPR] (see the top of this file),
# 'The random part' and 'The deterministic part': search at most <N>
# random elements a of std.G for g = t^a such that W = U + Ug has
# dimension n' and is non-degenerate, and U meets Fix(g) in a space with a
# hyperbolic pair, which spans P'; then conjugate g by b in <Y> mapping P'
# onto P.
# <Y> and <R> are the standard generators of CL(n,q) with memory and their
# root elements. Returns either fail, or else a record with the following
# components:
#  - `a`: the random element, with memory in the generators of std.G
#  - `t`: the seed, as a word with memory in <Y>
#  - `b`: as a word with memory in <Y>
#  - `g`: the matrix of g~ = (t^a)^b relative to std.bas
RECOG.Form_GoingUpDoublingElement := function(std, Y, R, N)
  local f, d, n, nn, form, Ubasis, Ystd, p, t, tmat, a, amat, g, Ug, Ufix,
        pair, b, b2, bmat;

  f := std.f;
  d := std.d;
  n := std.n;
  nn := Minimum(2 * n - 2, d);
  form := RECOG.ClassicalForm(std.type, d, f);
  Ubasis := IdentityMat(d, f){[1 .. n]};
  Ystd := RECOG.ClassicalStandardGenerators(std.type, n, f);
  p := Characteristic(f);
  t := RECOG.Form_GoingUpSeed(R, n, p);
  tmat := RECOG.GoingUpEmbed(RECOG.Form_GoingUpSeed(Ystd, n, p), d, f);

  repeat
    if N = 0 then
      return fail;
    fi;
    N := N - 1;
    pair := fail;
    a := PseudoRandom(std.G);
    amat := std.bas * StripMemory(a) * std.basi;
    g := amat^-1 * tmat * amat;

    Ug := SemiEchelonMat(Concatenation(Ubasis, g{[1 .. n]})).vectors;
    if Length(Ug) <> nn then
      continue;
    fi;
    if nn < d and RankMat(RECOG.FormGram(form, Ug)) <> nn then
      continue;
    fi;

    Ufix := SumIntersectionMat(RECOG.FixspaceMat(g), Ubasis)[2];
    pair := RECOG.FormHyperbolicPair(form, Ufix);
  until pair <> fail;

  # b maps P' onto P: the hyperbolic pair to e_1 and f_1, followed by the
  # pair cycle v^(m-1), which maps the first pair to the last
  b := RECOG.Form_MapToStd(R, pair[1]{[1 .. n]});
  b2 := RECOG.Form_MapToF1FixingE1(R, pair[2]{[1 .. n]} * b.mat);
  bmat := b.mat * b2.mat * Ystd.v^(n / 2 - 1);
  b := b.word * b2.word * R.v^(n / 2 - 1);

  amat := RECOG.GoingUpEmbed(bmat, d, f);
  g := amat^-1 * g * amat;
  Assert(1, g{[n - 1, n]} = IdentityMat(d, f){[n - 1, n]});
  return rec( a := a, t := t, b := b, g := g );
end;

# Step 4 (Adapting the basis) of the GoingUp step of [EHNPR]: the matrix C
# of the basis change which keeps the first n vectors of std.bas, replaces
# the next n'-n by a standard basis of N, the projection to T of A <g>
# (rows 1 to n-2 of <g>), and the last d-n' by a standard basis of its
# orthogonal complement in T. The new basis is C * std.bas; for n' = d,
# N = T and C is the identity.
RECOG.Form_GoingUpAdaptBasis := function(std, g)
  local f, d, n, formT, N, rest;

  f := std.f;
  d := std.d;
  n := std.n;
  if 2 * n - 2 >= d then
    return IdentityMat(d, f);
  fi;

  formT := RECOG.ClassicalForm(std.type, d - n, f);
  N := SemiEchelonMat(g{[1 .. n - 2]}{[n + 1 .. d]}).vectors;
  N := RECOG.FormStandardBasis(formT, N);
  rest := NullspaceMat(formT.gram
                       * TransposedMat(RECOG.FormConjugate(formT, N)));
  rest := RECOG.FormStandardBasis(formT, rest);
  return DirectSumMat(IdentityMat(n, f), Concatenation(N, rest));
end;

# Step 5 of the GoingUp step ([EHNPR], 'Constructing the enlarged group'):
# the standard generators of CL(W), W = U + N, relative to the first n'
# vectors of the adapted basis, as words in the standard generators <Y> of
# CL(U) and g~, whose matrix relative to the adapted basis is <g>. They
# are those of CL(U) except the pair cycle v, which is
# v_W = tau_(m'-1) ... tau_m v_U, where tau_j swaps the pairs j and j+1.
# Each tau_j is a product of four transvections of W, which are conjugates
# of transvections of U. Returns the list of words, as elements with
# memory in generators standing for Y and g~.
RECOG.Form_GoingUpNewGenerators := function(std, Y, R, g)
  local f, d, n, nn, form, norm, F, RF, e, gi, Ub, Upb, Npb, Wb, coeffs,
        withNorm, mapInU, intoU, transvection, vpos, tau, v, j, a, b, res;

  f := std.f;
  d := std.d;
  n := std.n;
  nn := Minimum(2 * n - 2, d);
  form := RECOG.ClassicalForm(std.type, d, f);
  norm := w -> RECOG.FormValue(form, w, w);
  F := GeneratorsWithMemory(ListWithIdenticalEntries(Length(Y) + 1, ()));
  # root elements of CL(U) as words in the first generators of F
  RF := RECOG.GoingUpParameters(std.type).rootElementsOf(
            F{[1 .. Length(Y)]}, n, f);

  # W = U + N = U' + N' with U' = U g~ and N' = N g~, all as rows of length
  # d; N is spanned by the basis vectors n+1 to n'
  e := IdentityMat(d, f);
  gi := g^-1;
  Ub := e{[1 .. n]};
  Upb := g{[1 .. n]};
  Npb := g{[n + 1 .. nn]};
  Wb := Concatenation(Upb, Npb);
  coeffs := w -> SolutionMat(Wb, w);

  # a nonzero vector of z + P, P = <e_m, f_m> <= U meet U', of norm nu: z,
  # or z minus its component in P, of norm mu, plus e_m + c f_m, of norm
  # 2c = nu - mu
  withNorm := function(z, nu)
    if not IsZero(z) and norm(z) = nu then
      return z;
    fi;
    z := ShallowCopy(z);
    z[n - 1] := Zero(f);
    z[n] := Zero(f);
    z[n] := (nu - norm(z)) / 2;
    z[n - 1] := One(f);
    return z;
  end;

  # an element of CL(U), as a word in F, mapping y to z, both nonzero in U
  # and of the same norm
  mapInU := function(y, z)
    return RECOG.Form_MapToStd(RF, y{[1 .. n]}).word
           * RECOG.Form_MapToStd(RF, z{[1 .. n]}).word^-1;
  end;

  # A word h in Y and g~, and the vector wh in U, for nonzero w in W. Write
  # w = u' + x' with u' in U', x' in N'. Since U' projects onto N, the
  # vectors of U' with the projection to N of -x' are a coset of
  # U meet U', which contains a vector u'' of the norm of u'. An element of
  # CL(U') = CL(U)^g~ mapping u' to u'' fixes N' and maps w into U. If
  # u' = 0, the same with the roles of U, N and U', N' exchanged first maps
  # w into U'.
  intoU := function(w)
    local c, u, x, z, k, h;

    if IsZero(w{[n + 1 .. d]}) then
      return rec( word := F[1]^0, vector := w );
    fi;

    c := coeffs(w);
    if IsZero(c{[1 .. n]}) then
      u := Concatenation(w{[1 .. n]}, Zero(w{[n + 1 .. d]}));
      x := w - u;
      z := SolutionMat(List(Ub, y -> coeffs(y){[n + 1 .. nn]}),
                       -coeffs(x){[n + 1 .. nn]}) * Ub;
      z := withNorm(z, norm(u));
      k := mapInU(u, z);
      h := intoU(z + x);
      return rec( word := k * h.word, vector := h.vector );
    fi;

    u := c{[1 .. n]} * Upb;
    x := c{[n + 1 .. nn]} * Npb;
    z := SolutionMat(Upb{[1 .. n]}{[n + 1 .. nn]}, -x{[n + 1 .. nn]}) * Upb;
    z := withNorm(z, norm(u));
    k := mapInU(u * gi, z * gi);
    h := F[Length(F)]^-1 * k * F[Length(F)];
    Assert(1, IsZero((z + x){[n + 1 .. d]}));
    return rec( word := h, vector := z + x );
  end;

  # the transvection T(w, lambda) of W, w isotropic, as
  # T(e_1, lambda)^(h^-1) for h mapping w to e_1
  transvection := function(w, lambda)
    local h;
    h := intoU(w);
    h := h.word * RECOG.Form_MapToStd(RF, h.vector{[1 .. n]}).word;
    return h * RECOG.Form_RootElement(RF, "Le", 1, lambda) * h^-1;
  end;

  # tau_j = T(b, y) T(a, x) T(b, y) T(a, x), a = e_j - e_(j+1),
  # b = f_j - f_(j+1), with [x, y] = RF.tau ([EHNPR], 'Constructing the
  # enlarged group')
  vpos := Position(RECOG.ClassicalStandardGeneratorNames(std.type), "v");
  v := F[vpos];
  for j in [n / 2 .. nn / 2 - 1] do
    a := e[2 * j - 1] - e[2 * j + 1];
    b := e[2 * j] - e[2 * j + 2];
    tau := transvection(b, RF.tau[2]) * transvection(a, RF.tau[1]);
    v := tau * tau * v;
  od;
  res := F{[1 .. Length(Y)]};
  res[vpos] := v;
  return res;
end;
