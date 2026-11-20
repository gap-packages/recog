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
##  'GoingUp algorithm', specific to special linear groups.
##
##  Vectors are rows of coordinates relative to a basis (v_1, ..., v_d),
##  and <x|y> = x y^T is the standard scalar product, relative to which the
##  adjoint g^-* of g is the transposed inverse. E(i, j, lambda) denotes
##  the elementary matrix v_i -> v_i + lambda v_j, which is the
##  transvection T(lambda v_i, v_j): x -> x + <x|lambda v_i> v_j.
##
#############################################################################

# Elementary matrices of SL(<n>,q), q = Size(<f>), as words in the
# standard generators. <Y> are elements with memory standing for the
# standard generators of SL(n,q) relative to the basis, in the order of
# RECOG.ClassicalStandardGenerators; only their words are used, so they
# may be generators with memory of any group. RECOG.SL_ElementaryMatrix
# combines the words returned here.
# E(1, 2, gamma^(2k)) is t^(delta^-k), gamma = Z(q), and these gamma^(2k),
# 0 <= k < [GF(q):GF(p)], are a basis of GF(q) over GF(p); E(2, 1, lambda)
# is E(1, 2, -lambda)^s. The element c = s v (n odd) or s v x (n even) maps
# v_1 to -v_1 and permutes the lines <v_2>, ..., <v_n> in one cycle, so
# conjugating by its powers gives E(1, j, .) and E(j, 1, .); the others are
# commutators [E(i, 1, lambda), E(1, j, 1)] = E(i, j, lambda).
# This follows [EHNPR], 'Standard generators and stingray embeddings',
# with the words of 'Constructing the enlarged group', except for c:
# there c = v or v x cycles all of v_1, ..., v_n, and E(i, j, .) is a
# chain of commutators along the cycle; fixing <v_1> makes it a single
# commutator.
RECOG.SL_RootElements := function(Y, n, f)
  local s, t, delta, v, x, ext, gamma, res, std, c, cmat, h, images, j, k;

  s := Y[1];
  t := Y[2];
  delta := Y[3];
  v := Y[4];
  x := Y[5];
  ext := DegreeOverPrimeField(f);
  gamma := Z(Size(f));

  res := rec(
    f := f,
    Y := Y,
    one := s^0,
    basis := Basis(f, List([0 .. ext - 1], k -> gamma^(2 * k))),
    E12 := List([0 .. ext - 1], k -> t^(delta^-k)),
    conjugator := [],
    sign := [],
    words := List([1 .. n], i -> []),
  );
  res.E21 := List(res.E12, y -> (y^-1)^s);

  # conjugator[j] = c^k maps v_1 to +-v_1 and v_2 to +-v_j; for a signed
  # permutation matrix h, E(1, 2, lambda)^h = E(1, j, lambda * sign), with
  # sign the product of these two signs
  res.conjugator[2] := res.one;
  res.sign[2] := One(f);
  if n >= 3 then
    std := RECOG.ClassicalStandardGenerators("SL", n, f);
    if IsOddInt(n) then
      c := s * v;
      cmat := std.s * std.v;
    else
      c := s * v * x;
      cmat := std.s * std.v * std.x;
    fi;
    h := res.one;
    images := IdentityMat(n, f){[1, 2]};
    for k in [1 .. n - 2] do
      h := h * c;
      images := images * cmat;
      j := PositionNonZero(images[2]);
      res.conjugator[j] := h;
      res.sign[j] := images[2, j] * images[1, 1];
    od;
  fi;
  return res;
end;

# The elementary matrix E(<i>, <j>, <lambda>) of RECOG.SL_RootElements, as
# a word in R.Y. R.words[i][j][k] keeps the powers of E(i, j, b), b the
# k-th vector of R.basis, for RECOG.GoingUpRootWord.
RECOG.SL_ElementaryMatrix := function(R, i, j, lambda)
  local words, signed, y;

  if not IsBound(R.words[i][j]) then
    # E(1, 2, b)^(+-1)
    signed := function(y, sign)
      if IsOne(sign) then
        return y;
      fi;
      return y^-1;
    end;
    if i = 1 then
      words := List(R.E12, y -> signed(y, R.sign[j])^R.conjugator[j]);
    elif j = 1 then
      words := List(R.E21, y -> signed(y, R.sign[i])^R.conjugator[i]);
    else
      # R.basis starts with 1
      y := RECOG.SL_ElementaryMatrix(R, 1, j, One(R.f));
      words := List([1 .. Length(R.E12)], k -> Comm(
          RECOG.SL_ElementaryMatrix(R, i, 1, BasisVectors(R.basis)[k]), y));
    fi;
    R.words[i][j] := List(words, y -> [y]);
  fi;
  return RECOG.GoingUpRootWord(R.words[i][j], R.basis, lambda, R.one);
end;

# A word for the matrix <M> in SL(n,q), as a product of the elementary
# matrices E(i, j, lambda) = <E>(i, j, lambda), which may be words in
# anything; <one> is the identity among them. Row reduction of M^-1 by
# adding multiples of rows only, as in RECOG.ExpressInStd_SL: each row
# operation multiplies by an elementary matrix from the left, and their
# product is M. Clearing below the diagonal first and above it last keeps
# rows sparse: a signed permutation matrix takes O(n) row operations,
# instead of O(n^2) when each column is cleared completely at once.
RECOG.SL_ExpressByElementary := function(M, E, one)
  local n, X, word, rowOp, i, pos, j;

  n := NrRows(M);
  X := MutableCopyMat(M^-1);
  word := one;
  # row i := row i + lambda * row j
  rowOp := function(i, j, lambda)
    X[i] := X[i] + lambda * X[j];
    word := E(i, j, lambda) * word;
  end;

  for i in [1 .. n] do
    if not IsOne(X[i, i]) then
      pos := First([i + 1 .. n], k -> not IsZero(X[k, i]));
      if pos = fail then
        # then X[i,i] is the only nonzero entry of column i in rows >= i
        pos := i + 1;
        rowOp(pos, i, One(X[i, i]));
      fi;
      rowOp(i, pos, (1 - X[i, i]) / X[pos, i]);
    fi;
    for j in [i + 1 .. n] do
      if not IsZero(X[j, i]) then
        rowOp(j, i, -X[j, i]);
      fi;
    od;
  od;

  # X is upper unitriangular; row i is v_i once the columns after i are
  # cleared
  for i in [n, n - 1 .. 2] do
    for j in [1 .. i - 1] do
      if not IsZero(X[j, i]) then
        rowOp(j, i, -X[j, i]);
      fi;
    od;
  od;
  return word;
end;

# An element b of SL(n,q) which maps the nonzero vector <u> to v_n, by
# Gaussian elimination on u with elementary matrices, as in Step 3 of the
# GoingUp step of [EHNPR].
# Returns a record with the following components:
#  - `word`: b, as a word in R.Y
#  - `mat`: the matrix of b
RECOG.SL_MapToLast := function(R, u)
  local n, word, mat, apply, i, r;

  n := Length(u);
  word := R.one;
  mat := MutableCopyMat(IdentityMat(n, R.f));
  # u E(i, j, lambda) = u + lambda u_i v_j, and M E(i, j, lambda) adds
  # lambda times column i of M to column j
  apply := function(i, j, lambda)
    word := word * RECOG.SL_ElementaryMatrix(R, i, j, lambda);
    u[j] := u[j] + lambda * u[i];
    for r in [1 .. n] do
      mat[r, j] := mat[r, j] + lambda * mat[r, i];
    od;
  end;

  u := ShallowCopy(u);
  if IsZero(u[n]) then
    i := PositionNonZero(u);
    apply(i, n, One(u[i]));
  fi;
  if not IsOne(u[n]) then
    i := PositionNonZero(u);
    if i = n then
      apply(n, 1, One(u[n]));
      i := 1;
    fi;
    apply(i, n, (1 - u[n]) / u[i]);
  fi;
  for i in [1 .. n - 1] do
    if not IsZero(u[i]) then
      apply(n, i, -u[i]);
    fi;
  od;

  Assert(1, u = IdentityMat(n, R.f)[n]);
  return rec( word := word, mat := mat );
end;

# The seed t of the GoingUp step ([EHNPR], Step 1 (Constructing the seed
# element)): a word in the standard generators <Y> of SL(n,q), q a power
# of <p>, with a fixed space of dimension 1; <Y> may be words or the
# matrices. For n odd, the signed cycle v has the characteristic
# polynomial x^n - 1, in which 1 is a simple root if p does not divide n;
# otherwise s v, with (x + 1)(x^(n-1) - 1). For n even, t v fixes only
# f_1 + ... + f_m.
RECOG.SL_GoingUpSeed := function(Y, n, p)
  if IsEvenInt(n) then
    return Y[2] * Y[4];
  elif n mod p <> 0 then
    return Y[4];
  fi;
  return Y[1] * Y[4];
end;

# Steps 1 to 3 of the GoingUp step of [EHNPR] (see ../GoingUp.gi), 'The
# random part' and 'The deterministic part', for SL: search at most <N>
# random elements a of std.G for g = t^a such that U + Ug has
# dimension n' = min(2n - 1, d), U + Ug and the fixed vectors of g in T
# span V, and, for a fixed vector u of g in U and the hyperplane H of the
# vectors of U orthogonal to u, U + H g^-* has dimension n'; then
# conjugate g by b in <Y> mapping u to v_n. <Y> and <R> are the standard
# generators of SL(n,q) with memory and their root elements. Returns
# either fail, or else a record with the following components:
#  - `a`: the random element, with memory in the generators of std.G
#  - `t`: the seed, as a word with memory in <Y>
#  - `b`: as a word with memory in <Y>
#  - `g`: the matrix of g~ = (t^a)^b relative to std.bas
RECOG.SL_GoingUpDoublingElement := function(std, Y, R, N)
  local f, d, n, nn, e, Ubasis, Tbasis, t, tmat, a, amat, g, Ug, fix, u, H,
        accepted, b;

  f := std.f;
  d := std.d;
  n := std.n;
  nn := Minimum(2 * n - 1, d);
  e := IdentityMat(d, f);
  Ubasis := e{[1 .. n]};
  Tbasis := e{[n + 1 .. d]};
  t := RECOG.SL_GoingUpSeed(Y, n, Characteristic(f));
  tmat := RECOG.GoingUpEmbed(RECOG.SL_GoingUpSeed(
              RECOG.ClassicalStandardGenerators("SL", n, f).all, n,
              Characteristic(f)), d, f);

  repeat
    if N = 0 then
      return fail;
    fi;
    N := N - 1;
    accepted := false;
    a := PseudoRandom(std.G);
    amat := std.bas * StripMemory(a) * std.basi;
    g := amat^-1 * tmat * amat;

    Ug := SemiEchelonMat(Concatenation(Ubasis, g{[1 .. n]})).vectors;
    if Length(Ug) <> nn then
      continue;
    fi;
    fix := RECOG.FixspaceMat(g);
    if RankMat(Concatenation(Ug, SumIntersectionMat(fix, Tbasis)[2])) <> d
       then
      continue;
    fi;

    u := SumIntersectionMat(fix, Ubasis)[2][1];
    H := List(NullspaceMat(TransposedMat([u{[1 .. n]}])),
              h -> Concatenation(h, Zero(e[1]){[n + 1 .. d]}));
    ConvertToMatrixRep(H, f);
    accepted := RankMat(Concatenation(Ubasis, H * TransposedMat(g^-1))) = nn;
  until accepted;

  b := RECOG.SL_MapToLast(R, u{[1 .. n]});
  amat := RECOG.GoingUpEmbed(b.mat, d, f);
  g := amat^-1 * g * amat;
  Assert(1, g[n] = e[n]);
  return rec( a := a, t := t, b := b.word, g := g );
end;

# Step 4 (Adapting the basis) of the GoingUp step of [EHNPR] for SL: the
# matrix C of the basis change which keeps the first n vectors of
# std.bas, replaces the next n'-n by a basis of N, the projection to T of
# A <g> (rows 1 to n-1 of <g>), and the last d-n' by fixed vectors of <g>
# in T which complement N. The new basis is C * std.bas; for n' = d,
# N = T and C is the identity.
RECOG.SL_GoingUpAdaptBasis := function(std, g)
  local f, d, n, N, fix, k, T, rest;

  f := std.f;
  d := std.d;
  n := std.n;
  if 2 * n - 1 >= d then
    return IdentityMat(d, f);
  fi;

  N := SemiEchelonMat(g{[1 .. n - 1]}{[n + 1 .. d]}).vectors;
  fix := SumIntersectionMat(RECOG.FixspaceMat(g),
                            IdentityMat(d, f){[n + 1 .. d]})[2];
  fix := fix{[1 .. Length(fix)]}{[n + 1 .. d]};

  # The semi-echelon basis of the rows of N and fix, found in this order,
  # extends one of N by vectors independent modulo N. Their parts in the
  # span of fix are fixed vectors congruent to them modulo N.
  k := Length(N);
  T := SemiEchelonMatTransformation(Concatenation(N, fix));
  rest := T.coeffs{[k + 1 .. Length(T.coeffs)]}{[k + 1 .. k + Length(fix)]}
          * fix;
  return DirectSumMat(IdentityMat(n, f), Concatenation(N, rest));
end;

# Step 5 of the GoingUp step for SL ([EHNPR], 'Constructing the enlarged
# group'): the standard generators of SL(W), W = <v_1, ..., v_n'>,
# relative to the adapted basis, as words in the standard generators <Y>
# of SL(U) and g~, whose matrix relative to the adapted basis is <g>. s, t
# and delta are those of SL(U); v and x are products of elementary
# matrices of W, found by RECOG.SL_ExpressByElementary ([EHNPR] names
# Gaussian elimination but gives no words):
#  - E(i, j, .) with i, j <= n lies in SL(U);
#  - E(i, n, .) = T(w, v_n), w = lambda v_i, for i > n: write
#    w = a + b g^-* with a, b in <v_1, ..., v_(n-1)>; as g fixes v_n,
#    T(w, v_n) = T(a, v_n) T(b, v_n)^g;
#  - E(n, j, .) = T(v_n, w), w = lambda v_j, for j > n: for z in
#    <v_1, ..., v_(n-1)> with w the projection of zg to the new basis
#    vectors, and h the element T(r - v_n, v_n), r = v_n g^-*, of the
#    previous case, T(v_n, z)^(g h) = T(v_n, a + w) with a the part of zg
#    in <v_1, ..., v_(n-1)>;
#  - the others are commutators [E(i, n, lambda), E(n, j, 1)].
# Returns the list of words, as elements with memory in generators standing
# for Y and g~.
RECOG.SL_GoingUpNewGenerators := function(std, Y, R, g)
  local f, d, n, nn, F, G, RF, e, gis, toVnSolver, fromVnSolver, product,
        toVn, r, h, fromVn, compute, unit, elementary, new;

  f := std.f;
  d := std.d;
  n := std.n;
  nn := Minimum(2 * n - 1, d);
  F := GeneratorsWithMemory(ListWithIdenticalEntries(Length(Y) + 1, ()));
  G := F[Length(F)];
  # elementary matrices of SL(U) as words in the first generators of F
  RF := RECOG.SL_RootElements(F{[1 .. Length(Y)]}, n, f);
  e := IdentityMat(d, f);
  gis := TransposedMat(g^-1);
  toVnSolver := RECOG.GoingUpSolver(
      Concatenation(e{[1 .. n - 1]}, gis{[1 .. n - 1]}){[1 .. 2 * n - 2]}
      {[1 .. nn]});
  fromVnSolver := RECOG.GoingUpSolver(g{[1 .. n - 1]}{[n + 1 .. nn]});

  # the product of the E(i, j, c[i]) or E(j, i, c[i]), i < n, as a word in Y
  product := function(c, j, toJ)
    local res, i;
    res := RF.one;
    for i in [1 .. n - 1] do
      if IsZero(c[i]) then
        continue;
      elif toJ then
        res := res * RECOG.SL_ElementaryMatrix(RF, i, j, c[i]);
      else
        res := res * RECOG.SL_ElementaryMatrix(RF, j, i, c[i]);
      fi;
    od;
    return res;
  end;

  # T(w, v_n) for w in <v_1, ..., v_(n-1), v_(n+1), ..., v_n'>
  toVn := function(w)
    local c;
    c := toVnSolver(w{[1 .. nn]});
    return product(c{[1 .. n - 1]}, n, true)
           * product(c{[n .. 2 * n - 2]}, n, true)^G;
  end;

  r := e[n] * gis;
  if r = e[n] then
    h := F[1]^0;
  else
    h := toVn(r - e[n]);
  fi;

  # T(v_n, w) for w in <v_(n+1), ..., v_n'>
  fromVn := function(w)
    local z, a;
    z := fromVnSolver(w{[n + 1 .. nn]});
    a := (Concatenation(z, Zero(e[1]){[n .. d]}) * g){[1 .. n - 1]};
    return product(a, n, false)^-1 * product(z, n, false)^(G * h);
  end;

  # E(i, j, lambda) for i > n or j > n
  compute := function(i, j, lambda)
    if j = n then
      return toVn(lambda * e[i]);
    elif i = n then
      return fromVn(lambda * e[j]);
    fi;
    return Comm(elementary(i, n, lambda), elementary(n, j, One(f)));
  end;

  # E(i, j, lambda) = E(i, j, 1)^lambda for lambda in GF(p), so the powers
  # of E(i, j, 1) are kept
  unit := List([1 .. nn], i -> []);
  elementary := function(i, j, lambda)
    if i <= n and j <= n then
      return RECOG.SL_ElementaryMatrix(RF, i, j, lambda);
    elif not lambda in GF(Characteristic(f)) then
      return compute(i, j, lambda);
    elif not IsBound(unit[i][j]) then
      unit[i][j] := [compute(i, j, One(f))];
    fi;
    return RECOG.GoingUpPower(unit[i][j], IntFFE(lambda));
  end;

  new := RECOG.ClassicalStandardGenerators("SL", nn, f);
  return Concatenation(F{[1 .. 3]},
      List([new.v, new.x],
           M -> RECOG.SL_ExpressByElementary(M, elementary, F[1]^0)));
end;
