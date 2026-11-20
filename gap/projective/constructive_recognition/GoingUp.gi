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
##  GoingUp for classical groups in their natural representation, as in
##  [EHNPR] (see GoingDown.gi), Section 'GoingUp algorithm', for SL, for Sp
##  and SU in odd characteristic, and for orthogonal groups.
##
##  A GoingUp step ([EHNPR], 'The GoingUpStep algorithm', whose steps are
##  numbered as here) starts from a stingray embedding: a basis B of
##  V = GF(q)^d, a standard basis for the types with a form, whose first n
##  vectors span U, and words for the standard generators Y of CL(U)
##  relative to these vectors, extended by the identity on
##  T = <v_(n+1), ..., v_d>. With the
##  overlap k = 1 for SL and 2 otherwise, it constructs the same for
##  degree n' = min(2n - k, d), keeping the first n vectors of B, except
##  for SL in step 5:
##
##     U = A + P, P = <v_(n-k+1), ..., v_n> the pivot space
##     1. t in <Y> whose fixed space on U has dimension k (the seed)
##     2. g = t^a for random a, until W = U + Ug has dimension n', T meets
##        Fix(g) in a complement of W (for the types with a form: W is
##        non-degenerate, and of type + for orthogonal groups if n' < d),
##        and U meets Fix(g) in a suitable k-space P'
##     3. g~ = g^b with b in <Y> mapping P' onto P, so that g~ fixes P
##     4. v_(n+1), ..., v_d := a basis of N, the projection of A g~ to T,
##        and fixed vectors of g~ in T (for the types with a form: standard
##        bases of N and of its orthogonal complement in T); so W = U + N
##     5. the standard generators of CL(W) as words in Y and g~; for SL
##        mostly relative to a new basis of W, in which a short word in Y
##        and g~ is almost the long cycle (see SL/GoingUp.gi)
##
##  For an orthogonal group, CL(U) is Omega^+(n,q), and so is CL(W) unless
##  n' = d.
##
#############################################################################

# Random selections a GoingUp step may make before it returns fail
RECOG.GoingUpRandomBound := 100;

# The functions of the GoingUp step for the classical type <type>, and its
# overlap k (see the top of this file). rootElements(n, f) returns the
# record of root elements of CL(n,q), whose component Y holds the words
# standing for the standard generators; for the types with a form,
# rootElementsOf(Y, n, f) returns it for given words Y, and seed(Y, n, p)
# is the seed. For orthogonal groups these are those of Omega^+(n,q). The
# other functions are documented where they are defined, in SL/GoingUp.gi,
# Omega/GoingUp.gi and below.
RECOG.GoingUpParameters := function(type)
  local of, k, res;

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
  elif type = "SU" then
    of := RECOG.SU_RootElements;
  elif type in RECOG.OrthogonalTypes then
    of := RECOG.Omega_RootElements;
  else
    ErrorNoReturn("RECOG.GoingUpParameters: unsupported type ", type);
  fi;
  k := Length(RECOG.ClassicalStandardGeneratorNames(
                  RECOG.ClassicalPrefixType(type)));
  res := rec( overlap := 2,
              rootElementsOf := of,
              rootElements := {n, f} -> of(
                  GeneratorsWithMemory(ListWithIdenticalEntries(k, ())), n, f),
              seed := RECOG.Form_GoingUpSeed,
              doublingElement := RECOG.Form_GoingUpDoublingElement,
              adaptBasis := RECOG.Form_GoingUpAdaptBasis,
              newGenerators := RECOG.Form_GoingUpNewGenerators );
  if type in RECOG.OrthogonalTypes then
    res.seed := RECOG.Omega_GoingUpSeed;
    res.newGenerators := RECOG.Omega_GoingUpNewGenerators;
  elif type = "SU" then
    res.newGenerators := RECOG.SU_GoingUpNewGenerators;
  fi;
  return res;
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

# The largest exponent whose power RECOG.GoingUpPower keeps; c < p, so
# larger bounds make the cache grow with p
RECOG.GoingUpPowerCacheBound := 1000;

# <powers>[1]^<c> for an integer c > 0, as the product of the
# powers[1]^(2^k) for the binary digits of c, so that the SLP of a word
# with memory computes each square once. powers[2] keeps them: twos[k] is
# powers[1]^(2^(k-1)), and cache[c] the result for
# c <= RECOG.GoingUpPowerCacheBound.
RECOG.GoingUpPower := function(powers, c)
  local store, keep, res, e, k;

  if not IsBound(powers[2]) then
    powers[2] := rec( twos := [powers[1]], cache := [] );
  fi;
  store := powers[2];
  keep := c <= RECOG.GoingUpPowerCacheBound;
  if keep and IsBound(store.cache[c]) then
    return store.cache[c];
  fi;

  res := fail;
  e := c;
  k := 1;
  while e > 0 do
    if k > Length(store.twos) then
      store.twos[k] := store.twos[k - 1]^2;
    fi;
    if IsOddInt(e) then
      if res = fail then
        res := store.twos[k];
      else
        res := res * store.twos[k];
      fi;
    fi;
    e := QuoInt(e, 2);
    k := k + 1;
  od;

  if keep then
    store.cache[c] := res;
  fi;
  return res;
end;

# A table of the words of one root group for RECOG.GoingUpRootWord, with
# <words>[k] the root element for the k-th basis vector: `powers[k]` is a
# list for RECOG.GoingUpPower, and `words` keeps the root elements built
# so far by the code of their parameter, so that each is one node of the
# SLP however often it is used.
RECOG.GoingUpRootTable := words -> rec( powers := List(words, y -> [y]),
                                        words := rec() );

# The root element for <lambda> in GF(q), as the product of the
# words[k]^c_k for the coefficients c_k of lambda in <basis>, a basis of
# GF(q) or a subspace over GF(p), with the words of the table <table> of
# RECOG.GoingUpRootTable. Root elements in one root group are additive in
# lambda. Factors with c_k = 0 are left out, and <one> stands for
# lambda = 0. Returns the word and a code of lambda, an integer in
# [0 .. q-1] which is 0 for lambda = 0 only: 1 + LogFFE(lambda, z) for z
# the primitive root of the field of the basis vectors, or, for fields
# larger than GAP's internal ones, c_1 + c_2 p + c_3 p^2 + ...
RECOG.GoingUpRootWordCode := function(table, basis, lambda, one)
  local coeffs, p, code, res, k, y;

  if IsZero(lambda) then
    return [one, 0];
  fi;
  if not IsBound(table.root) then
    table.root := PrimitiveRoot(DefaultField(BasisVectors(basis)));
  fi;
  coeffs := fail;
  if IsInternalRep(lambda) then
    code := LogFFE(lambda, table.root) + 1;
  else
    coeffs := List(Coefficients(basis, lambda), IntFFE);
    p := Characteristic(lambda);
    code := 0;
    for k in [Length(coeffs), Length(coeffs) - 1 .. 1] do
      code := code * p + coeffs[k];
    od;
  fi;

  if not IsBound(table.words.(code)) then
    if coeffs = fail then
      coeffs := List(Coefficients(basis, lambda), IntFFE);
    fi;
    res := fail;
    for k in [1 .. Length(coeffs)] do
      if coeffs[k] = 0 then
        continue;
      fi;
      y := RECOG.GoingUpPower(table.powers[k], coeffs[k]);
      if res = fail then
        res := y;
      else
        res := res * y;
      fi;
    od;
    table.words.(code) := res;
  fi;
  return [table.words.(code), code];
end;

# The word of RECOG.GoingUpRootWordCode
RECOG.GoingUpRootWord := {table, basis, lambda, one} ->
    RECOG.GoingUpRootWordCode(table, basis, lambda, one)[1];

# The number b of consecutive slots per block of RECOG.GoingUpProduct in
# degree <n> over GF(<q>), with <k> parameters per slot: the q^(b k)
# products of a block must be few against the about n products on the
# same root elements. b = 0 turns the sharing off. Measured for q = 3, 9,
# 121 and n up to 1000.
RECOG.GoingUpBlockSize := {n, q, k} -> LogInt(n, q^k);

# A product of root words, built factor by factor, which shares the
# products of blocks of consecutive factors with all products built on
# the same <trie>, a record rec( next := rec() ) kept by the caller, as
# the four Russians method shares partial sums: the factors of a block
# follow a path of trie nodes, each holding the product so far, so a
# block met before costs one multiplication. A factor is given by its
# block number, an integer key unique for it among the root elements on
# the trie, and its word; the product starts with <one>, and factors
# identical to <one> are left out.
# `mul(block, key, y)` multiplies by y in that block, `mulPlain(y)` by y
# outside any block, and `word()` returns the product.
RECOG.GoingUpProduct := function(trie, one)
  local word, node, block, times, flush;

  word := one;
  node := fail;
  block := fail;
  times := function(y)
    if IsIdenticalObj(y, one) then
      return;
    elif IsIdenticalObj(word, one) then
      word := y;
    else
      word := word * y;
    fi;
  end;
  flush := function()
    if node <> fail then
      times(node.word);
      node := fail;
    fi;
  end;
  return rec(
    mul := function(blk, key, y)
      if node = fail or blk <> block then
        flush();
        node := trie;
        block := blk;
      fi;
      if not IsBound(node.next.(key)) then
        if IsIdenticalObj(node, trie) then
          node.next.(key) := rec( word := y, next := rec() );
        else
          node.next.(key) := rec( word := node.word * y, next := rec() );
        fi;
      fi;
      node := node.next.(key);
    end,
    mulPlain := function(y)
      flush();
      times(y);
    end,
    word := function()
      flush();
      return word;
    end );
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
# from them, not the MSLPs of [EHNPR]. params.newGenerators returns the
# list of words relative to the adapted basis C * std.bas, a record with
# the words relative to the basis M * C * std.bas and the matrix M as
# components `words` and `basis`, or fail to have the step repeated.
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
  if words = fail then
    return fail;
  elif IsRecord(words) then
    C := words.basis * C;
    ConvertToMatrixRep(C, f);
    Ci := C^-1;
    words := words.words;
  fi;

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
# algorithm') for the type <type>, "SL", or "Sp" (q odd, d even), "SU",
# or an orthogonal type ("O+" or "O-" for q even): <G> is
# SL(d,q), resp. Sp(d,q), SU(d,q0) or Omega(d,q) for some alternating,
# hermitian resp. symmetric or quadratic form, with
# generators with memory, and <init> describes an embedded CL(n,q), of type
# "O+" for orthogonal groups, as follows:
#  - `slp`: SLP in the generators of <G> for the standard generators of
#    CL(n,q), as in RECOG.ClassicalStandardGenerators, relative to bas
#  - `bas`: a d x d matrix whose last d-n rows are fixed by that CL(n,q);
#    for the types with a form, its rows are a standard basis of V for a
#    multiple of the form of <G>
#  - `n`: the degree n, at least 2 for SL, 4 for Sp and SU, and 6 for
#    orthogonal groups, where n/2 must be odd
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
##  The GoingUp step for the types with a form, Sp and SU, q odd, and its
##  parts which orthogonal groups share (see Omega/GoingUp.gi).
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
##  elements of RECOG.Sp_RootElements resp. RECOG.SU_RootElements and of a
##  torus element, found by elimination, which yields each word together
##  with its matrix.
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
##   - `tau` (q odd): the parameters [x, y] of the factors T(a, x) and
##     T(b, y) of tau_j in RECOG.Form_GoingUpNewGenerators
##   - for each kind of root element below, the component of that name, the
##     root elements kind(2, lambda) for lambda in the GF(p)-basis
##     bases.(kind) of their parameters
##   - `conjugator`: conjugator[j] maps e_2 to e_j and f_2 to f_j, and fixes
##     e_1, f_1, and `powers`: a cache for RECOG.Form_RootElement
##   - `trie`, `block`, `trieDegree`: the shared products of
##     RECOG.Form_Product, made by its first call
##   - `aniso` (only orthogonal groups of type - or o, see Rewrite.gi, and
##     SU of odd degree, see SU/Rewrite.gi): a record with components
##     `pos`, the indices of the basis w_1 (and w_2) of the anisotropic
##     part, which follows the m hyperbolic pairs, `pairs`, the number m,
##     `gram`, the Gram matrix on <w_1, w_2> resp. <w_1>, `unit`, the
##     parameter of w_1, `toField`, a function mapping a vector z of the
##     anisotropic part to the parameter of Fw(z) and Ew(z) in bases.Fw and
##     bases.Ew, for q even `quad`, the matrix of Q on <w_1, w_2> (see
##     RECOG.ClassicalForm), and for SU `lambda`, see below
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
##     f_1 -> f_1 - lambda^sigma f_j;
##   - with `aniso`, for z in the anisotropic part, the Siegel
##     transformations Fw(z) = rho(f_1, z): e_1 -> e_1 - z - Q(z) f_1,
##     w_i -> w_i + beta(w_i, z) f_1, and Ew(z) = rho(e_1, z): f_1 -> f_1 -
##     z - Q(z) e_1, w_i -> w_i + beta(w_i, z) e_1; for SU, -Q(z) is
##     lambda(kind, z) with kind = "Fw" resp. "Ew".
##
#############################################################################

# The root element <kind>(<j>, <lambda>) of <R>, as a word in R.Y, where
# <kind> is one of "Lf", "Le", "See", "Sff", "M1j", "Mj1", "Fw", "Ew",
# and <j> is ignored for "Lf", "Le", "Fw" and "Ew". R.powers.(kind)[j]
# is the table of RECOG.GoingUpRootTable for the conjugates of R.(kind) by
# R.conjugator[j], with j = 2 for the kinds without j. Returns the word
# and the code of RECOG.GoingUpRootWordCode.
RECOG.Form_RootElementCode := function(R, kind, j, lambda)
  local powers;

  if kind in ["Fw", "Ew"] then
    lambda := R.aniso.toField(lambda);
  fi;
  if kind in ["Lf", "Le", "Fw", "Ew"] then
    j := 2;
  fi;
  powers := R.powers.(kind);
  if not IsBound(powers[j]) then
    if j = 2 then
      powers[j] := RECOG.GoingUpRootTable(R.(kind));
    else
      powers[j] := RECOG.GoingUpRootTable(
                       List(R.(kind), y -> y^R.conjugator[j]));
    fi;
  fi;
  return RECOG.GoingUpRootWordCode(powers[j], R.bases.(kind), lambda, R.one);
end;

# The word of RECOG.Form_RootElementCode
RECOG.Form_RootElement := {R, kind, j, lambda} ->
    RECOG.Form_RootElementCode(R, kind, j, lambda)[1];

# The kinds of root elements on the pairs j >= 2, whose products
# RECOG.Form_Product shares, with their numbers
RECOG.Form_PairKinds := rec( See := 1, Sff := 2, M1j := 3, Mj1 := 4 );

# A product of root elements of <R>, a record of root elements of CL(n,q),
# as a word in R.Y, which shares the products of blocks of consecutive
# pairs with all products on R (see RECOG.GoingUpProduct); R keeps the
# trie. `apply(kind, j, lambda)` multiplies by the root element
# kind(j, lambda), the identity for lambda = 0, `mulPlain(y)` by the word
# y, and `word()` returns the product.
RECOG.Form_Product := function(R, n)
  local q, prod;

  q := Size(R.f);
  if not IsBound(R.trie) then
    R.trie := rec( next := rec() );
    R.block := RECOG.GoingUpBlockSize(n, q, 2);
    R.trieDegree := n;
  fi;
  n := R.trieDegree;
  prod := RECOG.GoingUpProduct(R.trie, R.one);
  return rec(
    apply := function(kind, j, lambda)
      local w;
      if IsZero(lambda) then
        return;
      fi;
      w := RECOG.Form_RootElementCode(R, kind, j, lambda);
      if R.block = 0 or not IsBound(RECOG.Form_PairKinds.(kind)) then
        prod.mulPlain(w[1]);
      else
        prod.mul(QuoInt(j - 2, R.block),
                 (RECOG.Form_PairKinds.(kind) * (n + 1) + j) * q + w[2], w[1]);
      fi;
    end,
    mulPlain := prod.mulPlain,
    word := prod.word );
end;

# The matrix of the root element <kind>(<j>, <lambda>) of <R> is the
# identity plus the entries c at the positions [i, k] of the triples
# [i, k, c] returned here. For "Fw" and "Ew" some k is also an i; the
# entries which read row i come before those which change it, so applying
# them in order acts as the matrix. These map the partner of a = f_1 resp.
# e_1 to it minus z plus lam a, with lam = -Q(z), or for SU of odd degree
# lam = R.aniso.lambda(kind, z) (see SU/Rewrite.gi).
RECOG.Form_RootElementEntries := function(R, kind, j, lambda)
  local c, a, pos, bz, res, i;

  if kind in ["Fw", "Ew"] then
    # rho(a, z) for a = f_1 resp. e_1, whose partner has the index 3 - a
    a := 2;
    if kind = "Ew" then
      a := 1;
    fi;
    pos := R.aniso.pos;
    # beta(w_i, z)
    bz := List(lambda * R.aniso.gram, R.conj);
    res := [];
    for i in [1 .. Length(pos)] do
      if not IsZero(bz[i]) then
        Add(res, [pos[i], a, bz[i]]);
      fi;
    od;
    for i in [1 .. Length(pos)] do
      if not IsZero(lambda[i]) then
        Add(res, [3 - a, pos[i], -lambda[i]]);
      fi;
    od;
    if IsBound(R.aniso.lambda) then
      c := -R.aniso.lambda(kind, lambda);
    elif IsBound(R.aniso.quad) then
      c := lambda * R.aniso.quad * lambda;
    else
      c := (bz * lambda) / 2;
    fi;
    Add(res, [3 - a, a, -c]);
    return res;
  fi;

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
# element of <R>, built by elimination on the vector <y> of length n, for
# the list <opt> of optional arguments of RECOG.Form_MapToStd: `y` is y b,
# `MT` is b^T opt[1], in place, or b^T if opt is empty,
# `apply(kind, j, lambda)` multiplies b by the root element
# kind(j, lambda), `scale(k)` by R.torus^k, and `result()` returns the
# record of RECOG.Form_MapToStd, with b as a word in R.Y built by
# RECOG.Form_Product. Each entry of a root element costs O(n) field
# operations on MT.
RECOG.Form_Elimination := function(R, y, opt)
  local res, prod;

  res := rec( y := ShallowCopy(y) );
  prod := RECOG.Form_Product(R, Length(y));
  if Length(opt) = 0 then
    res.MT := MutableCopyMat(IdentityMat(Length(y), R.f));
    ConvertToMatrixRep(res.MT, R.f);
  else
    res.MT := opt[1];
  fi;
  res.apply := function(kind, j, lambda)
    local x;
    prod.apply(kind, j, lambda);
    # y r adds c y_i to y_k, and r^T M^T adds c times row i to row k
    for x in RECOG.Form_RootElementEntries(R, kind, j, lambda) do
      res.y[x[2]] := res.y[x[2]] + x[3] * res.y[x[1]];
      AddRowVector(res.MT[x[2]], res.MT[x[1]], x[3]);
    od;
  end;
  res.scale := function(k)
    local i, c;
    prod.mulPlain(R.torus^k);
    for i in [1 .. Length(R.torusDiag)] do
      c := R.torusDiag[i]^k;
      res.y[i] := c * res.y[i];
      res.MT[i] := c * res.MT[i];
    od;
  end;
  res.result := function()
    if Length(opt) = 0 then
      return rec( word := prod.word(), mat := TransposedMat(res.MT) );
    fi;
    return rec( word := prod.word() );
  end;
  return res;
end;

# An element b of CL(n,q) which maps the nonzero vector <y> to
# e_1 + (nu/2) f_1, nu = beta(y, y), that is, to e_1 if y is isotropic, and
# to e_1 + Q(y) f_1 for orthogonal groups. It
# clears the coordinates of y one by one with root elements, as in
# Gaussian elimination, and scales the e_1-coordinate to 1 by the torus.
# Returns a record with the following components:
#  - `word`: b, as a word in R.Y
#  - `mat`: the matrix of b
# With the optional argument MT, the transpose of an n x n matrix M, `mat`
# is left out and MT is replaced by (M b)^T in place, in O(n^2) instead of
# O(n^3) field operations.
RECOG.Form_MapToStd := function(R, y, MT...)
  local n, m, elim, apply, j, z, nu;

  n := Length(y);
  m := n / 2;
  if IsBound(R.aniso) then
    m := R.aniso.pairs;
  fi;
  elim := RECOG.Form_Elimination(R, y, MT);
  apply := elim.apply;
  y := elim.y;

  # make the e_1-coordinate nonzero; without Le (orthogonal groups), for
  # y = c f_1 first f_1 -> f_1 + e_2, or, with an anisotropic part,
  # f_1 -> f_1 - w_1 - Q(w_1) e_1, which leaves the pairs alone
  if IsZero(y[1]) then
    if not IsZero(y[2]) and IsBound(R.Le) then
      apply("Le", 1, R.longUnit);
    else
      j := PositionNonZero(y, 2);
      if j > 2 * m and IsBound(R.aniso) then
        apply("Ew", 1, R.aniso.unit);
      else
        if j > 2 * m then
          apply("See", 2, One(R.f));
          j := 3;
        fi;
        if IsOddInt(j) then
          apply("Mj1", (j + 1) / 2, One(R.f));
        else
          apply("See", j / 2, One(R.f));
        fi;
      fi;
    fi;
  fi;

  # clear the other pairs and the anisotropic part, then make the
  # e_1-coordinate 1
  for j in [2 .. m] do
    if not IsZero(y[2 * j - 1]) then
      apply("M1j", j, -y[2 * j - 1] / y[1]);
    fi;
    if not IsZero(y[2 * j]) then
      apply("Sff", j, -y[2 * j] / y[1]);
    fi;
  od;
  if IsBound(R.aniso) then
    z := y{R.aniso.pos};
    if not IsZero(z) then
      apply("Fw", 1, z / y[1]);
    fi;
  fi;
  if not IsOne(y[1]) then
    elim.scale(LogFFE(y[1]^-1, R.gamma));
  fi;

  # y = e_1 + c f_1 has the norm nu = c^sigma + eps c, and nu/2 - c is a
  # parameter of Lf; nu = 0 for Sp; orthogonal groups have no Lf, and
  # c = Q(y). For SU in characteristic 2, nu h replaces nu/2, with
  # h = R.half of trace 1.
  if IsBound(R.Lf) then
    nu := R.conj(y[2]) + R.eps * y[2];
    if IsBound(R.half) then
      nu := nu * R.half;
    elif not IsZero(nu) then
      nu := nu / 2;
    fi;
    if y[2] <> nu then
      apply("Lf", 1, nu - y[2]);
    fi;
  fi;

  Assert(1, IsOne(y[1]) and IsZero(y{[3 .. n]}));
  return elim.result();
end;

# An element b of CL(n,q) which fixes e_1 and maps the isotropic vector
# <y> to f_1, where beta(e_1, y) = 1, as a record like that of
# RECOG.Form_MapToStd, with the same optional argument
RECOG.Form_MapToF1FixingE1 := function(R, y, MT...)
  local n, m, elim, apply, j, z;

  n := Length(y);
  m := n / 2;
  if IsBound(R.aniso) then
    m := R.aniso.pairs;
  fi;
  if not IsOne(y[2]) then
    ErrorNoReturn("RECOG.Form_MapToF1FixingE1: beta(e_1, <y>) must be 1");
  fi;
  elim := RECOG.Form_Elimination(R, y, MT);
  apply := elim.apply;
  y := elim.y;

  # these root elements fix e_1 and add multiples of the f_1-coordinate;
  # the last one clears the e_1-coordinate, as y is isotropic
  for j in [2 .. m] do
    if not IsZero(y[2 * j - 1]) then
      apply("See", j, -y[2 * j - 1]);
    fi;
    if not IsZero(y[2 * j]) then
      apply("Mj1", j, R.conj(y[2 * j]));
    fi;
  od;
  if IsBound(R.aniso) then
    z := y{R.aniso.pos};
    if not IsZero(z) then
      apply("Ew", 1, z);
    fi;
  fi;
  if not IsZero(y[1]) then
    apply("Le", 1, -R.eps * y[1]);
  fi;

  Assert(1, y = IdentityMat(n, R.f)[2]);
  return elim.result();
end;

# The seed t of the GoingUp step for Sp and SU ([EHNPR], Step 1
# (Constructing the seed element)): an element of CL(n,q), q a power of
# <p>, whose fixed space is a non-degenerate plane, given as a word in the
# components s, t, u, v of <Y>, which may be words or matrices.
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
# dimension n' and is non-degenerate, of type + for orthogonal groups if
# n' < d, and U meets Fix(g) in a space with a hyperbolic pair, which spans
# P'; then conjugate g by b in <Y> mapping P' onto P. With std.mixed (see
# RECOG.Sp_EvenGoingUp), the type refers to the quadratic form of
# RECOG.Sp_MixedQuadraticForm, which is kept as std.quad.
# <Y> and <R> are the standard generators of CL(n,q) with memory and their
# root elements. Returns either fail, or else a record with the following
# components:
#  - `a`: the random element, with memory in the generators of std.G
#  - `t`: the seed, as a word with memory in <Y>
#  - `b`: as a word with memory in <Y>
#  - `g`: the matrix of g~ = (t^a)^b relative to std.bas
RECOG.Form_GoingUpDoublingElement := function(std, Y, R, N)
  local f, d, n, nn, form, Ubasis, Ystd, p, seed, t, tmat, orth, a, amat, g,
        Ug, quad, Ufix, pair, b, b2, bmat;

  f := std.f;
  d := std.d;
  n := std.n;
  nn := Minimum(2 * n - 2, d);
  form := RECOG.ClassicalForm(std.type, d, f);
  Ubasis := IdentityMat(d, f){[1 .. n]};
  Ystd := RECOG.ClassicalStandardGenerators(
              RECOG.ClassicalPrefixType(std.type), n, f);
  p := Characteristic(f);
  seed := RECOG.GoingUpParameters(std.type).seed;
  t := seed(R, n, p);
  tmat := RECOG.GoingUpEmbed(seed(Ystd, n, p), d, f);
  orth := std.type in RECOG.OrthogonalTypes;

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
    if IsBound(std.mixed) then
      # the orthogonal chain in Sp(d,q), q even: the type refers to the
      # quadratic form which H and H^g preserve, also for n' = d
      quad := RECOG.Sp_MixedQuadraticForm(std, g);
      if quad = fail or RECOG.FormOrthogonalType(
             rec( gram := form.gram, frob := 1, field := f, quad := quad ),
             Ug) <> "O+" then
        continue;
      fi;
    elif nn < d and orth and RECOG.FormOrthogonalType(form, Ug) <> "O+" then
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
  if IsBound(std.mixed) then
    # b fixes T pointwise, so H^(g~) preserves the same form
    std.quad := quad;
  fi;
  return rec( a := a, t := t, b := b, g := g );
end;

# Step 4 (Adapting the basis) of the GoingUp step of [EHNPR]: the matrix C
# of the basis change which keeps the first n vectors of std.bas, replaces
# the next n'-n by a standard basis of N, the projection to T of A <g>
# (rows 1 to n-2 of <g>), and the last d-n' by a standard basis of its
# orthogonal complement in T. The new basis is C * std.bas; for n' = d,
# N = T and C is the identity. With std.quad, RECOG.Sp_MixedAdaptBasis.
RECOG.Form_GoingUpAdaptBasis := function(std, g)
  local f, d, n, formT, N, rest;

  f := std.f;
  d := std.d;
  n := std.n;
  if IsBound(std.quad) then
    return RECOG.Sp_MixedAdaptBasis(std, g);
  elif 2 * n - 2 >= d then
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

# A preimage z of <a> under the norm z -> z^(q^k + 1) of the field
# F[x]/(<f>) of order q^(2k), for <f> irreducible in the polynomial ring
# <R>, q odd, and a <> 0 in the subfield of order q^k: z = w b for a
# random w and a square root b of a / N(w) in that subfield, by
# Tonelli-Shanks.
RECOG.Form_NormPreimage := function(R, f, a, q, k)
  local x, randomElement, Q, S, w, b, c, t, r, M, i, s, z;

  x := IndeterminatesOfPolynomialRing(R)[1];
  randomElement := function()
    return Sum([0 .. DegreeOfLaurentPolynomial(f) - 1],
               i -> Random(CoefficientsRing(R)) * x^i);
  end;
  repeat
    w := randomElement();
    b := PowerMod(R, w, q^k + 1, f);
  until not IsZero(b) and PowerMod(R, (a * GcdRepresentation(R, b, f)[1]) mod f,
                                   (q^k - 1) / 2, f) = One(R);
  b := (a * GcdRepresentation(R, b, f)[1]) mod f;

  # a non-square c of the subfield, a norm
  repeat
    c := PowerMod(R, randomElement(), q^k + 1, f);
  until not IsZero(c) and PowerMod(R, c, (q^k - 1) / 2, f) <> One(R);
  Q := q^k - 1;
  S := 0;
  while IsEvenInt(Q) do
    Q := Q / 2;
    S := S + 1;
  od;
  M := S;
  c := PowerMod(R, c, Q, f);
  t := PowerMod(R, b, Q, f);
  r := PowerMod(R, b, (Q + 1) / 2, f);
  while t <> One(R) do
    i := 0;
    s := t;
    while s <> One(R) do
      s := (s * s) mod f;
      i := i + 1;
    od;
    z := PowerMod(R, c, 2^(M - i - 1), f);
    M := i;
    c := (z * z) mod f;
    t := (t * c) mod f;
    r := (r * z) mod f;
  od;
  z := (w * r) mod f;
  Assert(1, PowerMod(R, z, q^k + 1, f) = a mod f);
  return z;
end;

# A vector e of W = GF(q)^n, n = 2m, for the isometry <h> of the form
# beta(x, y) = x <J> y^(sigma T) of type <type>, "Sp", "SU" or "O+", over
# <F> (sigma the identity, resp. c -> c^q0 for F = GF(q0^2)), with
# squarefree characteristic polynomial <chi>, such that beta(e, e h^j) = 0
# for 0 <= j < k and beta(e, e h^k) <> 0, with k = m, resp. k = m - 1 for
# "O+", or fail. Then e, e h, ..., e h^(k-1) span a totally isotropic
# (singular) space, and for SU, where det h = 1, beta(e, e h^m) has
# trace 0.
# W is a cyclic F[h]-module: e = c p(h) for a cyclic vector c, and with
# phi(a) = beta(c, c a(h)), beta(e, e h^j) = phi(N x^j) for
# N = p p^dagger, a^dagger = a^sigma(x^-1), in A = F[x]/chi. The
# conditions on the self-adjoint N are linear over the fixed field of
# sigma, with a one-dimensional solution space <N0> in general, and the
# norm equation p p^dagger = N0 is solved in each factor of A: trivially
# for a pair of factors f, f^dagger, by RECOG.Form_NormPreimage for
# f = f^dagger otherwise, except for x - 1 and x + 1 in Sp and O+, where it
# is a square root.
RECOG.Form_IsotropicKrylovVector := function(h, J, F, chi, type)
  local n, m, q, q0, conj, R, x, c, K, cJ, i, phi, ph, F0, omega, coords,
        M, row, k, j, nu, cands, top, xi, N, N0, mods, rems, used, f, fs, a,
        z, p, P, coeffs, e, form;

  n := NrRows(h);
  m := n / 2;
  q := Size(F);
  if type = "SU" then
    q0 := RootInt(q);
    conj := v -> List(v, y -> y^q0);
  else
    q0 := q;
    conj := v -> v;
  fi;
  R := PolynomialRing(F, 1);
  x := IndeterminatesOfPolynomialRing(R)[1];

  repeat
    c := Random(F^n);
    K := [c];
    for i in [1 .. n] do
      Add(K, K[i] * h);
    od;
  until RankMat(K{[1 .. n]}) = n;
  cJ := c * J;
  phi := List(K, y -> cJ * conj(y));
  # phi(x^-i) = beta(c h^i, c), which is -phi(x^i), phi(x^i)^sigma resp.
  # phi(x^i)
  ph := function(i)
    if i >= 0 then
      return phi[i + 1];
    elif type = "SU" then
      return phi[1 - i]^q0;
    elif type = "O+" then
      return phi[1 - i];
    fi;
    return -phi[1 - i];
  end;

  # N = sum_k (nu_k x^k + nu_k^sigma x^-k), 0 <= k <= m, with
  # phi(N x^j) = 0 for 0 <= j < m, as GF(q0)-linear equations in the
  # coordinates of the nu_k in the basis 1, omega of F over GF(q0); for Sp
  # omega = 0, nu_m = 0, and phi(N) = 0 holds already
  if type = "SU" then
    # z = a + b omega with b = (z - z^sigma) / (omega - omega^sigma)
    omega := PrimitiveRoot(F);
    F0 := (omega - omega^q0)^-1;
    coords := function(z)
      local b;
      b := (z - z^q0) * F0;
      return [z - b * omega, b];
    end;
    M := [];
    for k in [0 .. m] do
      for nu in [One(F), omega] do
        row := [];
        for j in [0 .. m - 1] do
          Append(row, coords(nu^q0 * ph(k + j) + nu * ph(j - k)));
        od;
        Add(M, row);
      od;
    od;
    cands := List(NullspaceMat(M), v -> List([0 .. m],
                  k -> v[2 * k + 1] * One(F) + v[2 * k + 2] * omega));
  elif type = "O+" then
    # phi(N x^j) = 0 for 0 <= j < m - 1; the value at m - 1 is tested below
    M := List([0 .. m - 1], k -> List([0 .. m - 2],
                                      j -> ph(k + j) + ph(j - k)));
    cands := NullspaceMat(M);
    if Length(cands) <> 1 then
      return fail;
    fi;
    cands := [Concatenation(cands[1], [Zero(F)])];
  else
    M := List([0 .. m - 1], k -> List([1 .. m - 1],
                                      j -> ph(k + j) + ph(j - k)));
    cands := NullspaceMat(M);
    if Length(cands) <> 1 then
      return fail;
    fi;
    cands := [Concatenation(cands[1], [Zero(F)])];
  fi;

  # a nu with N <> 0 and phi(N x^top) <> 0, top = m resp. m - 1 for "O+"
  top := m;
  if type = "O+" then
    top := m - 1;
  fi;
  xi := GcdRepresentation(R, x, chi)[1] mod chi;
  N0 := fail;
  for nu in cands do
    if not IsZero(Sum([0 .. m], k -> nu[k + 1]^q0 * ph(k + top)
                                     + nu[k + 1] * ph(top - k))) then
      N := Sum([0 .. m], k -> nu[k + 1] * x^k
                          + nu[k + 1]^q0 * PowerMod(R, xi, k, chi)) mod chi;
      if not IsZero(N) then
        N0 := N;
        break;
      fi;
    fi;
  od;
  if N0 = fail then
    return fail;
  fi;

  # p, with p p^dagger = N0, by the Chinese remainder theorem
  mods := [];
  rems := [];
  used := [];
  for f in Factors(R, chi) do
    if f in used then
      continue;
    fi;
    a := N0 mod f;
    coeffs := conj(CoefficientsOfUnivariatePolynomial(f));
    fs := UnivariatePolynomial(F, Reversed(coeffs) / coeffs[1]);
    Add(used, f);
    if fs <> f then
      Append(mods, [f, fs]);
      Append(rems, [a, One(R)]);
      Add(used, fs);
    elif type <> "SU" and DegreeOfLaurentPolynomial(f) = 1 then
      z := RootsOfUPol(F, x^2 - Value(a, Zero(F)));
      if z = [] then
        return fail;
      fi;
      Add(mods, f);
      Add(rems, z[1] * One(R));
    elif type <> "SU" then
      Add(mods, f);
      Add(rems, RECOG.Form_NormPreimage(R, f, a, q,
                                        DegreeOfLaurentPolynomial(f) / 2));
    else
      Add(mods, f);
      Add(rems, RECOG.Form_NormPreimage(R, f, a, q0,
                                        DegreeOfLaurentPolynomial(f)));
    fi;
  od;
  p := rems[1] mod mods[1];
  P := mods[1];
  for j in [2 .. Length(mods)] do
    p := p + P * (((rems[j] - p) * GcdRepresentation(R, P mod mods[j],
                                                     mods[j])[1]) mod mods[j]);
    P := P * mods[j];
  od;
  p := p mod chi;

  # e = c p(h), from the vectors c h^i
  coeffs := CoefficientsOfUnivariatePolynomial(p);
  e := Sum([1 .. Length(coeffs)], i -> coeffs[i] * K[i]);
  form := {y, z} -> y * J * conj(z);
  Assert(1, ForAll([0 .. top - 1], j -> IsZero(form(e, e * h^j)))
            and not IsZero(form(e, e * h^top)));
  return e;
end;

# The elements a of CL(U) on the first pair tried by
# RECOG.Form_GoingUpCycleBasis, as functions of a record with components
# s, t and delta (words or matrices), in this order
RECOG.Form_GoingUpCycleSeeds := [Y -> Y.s, Y -> Y.delta, Y -> Y.s^-1,
    Y -> Y.s * Y.t, Y -> Y.s^0, Y -> Y.t, Y -> Y.t^-1, Y -> Y.delta^-1];

# The number of new doubling elements a GoingUp step for Sp or SU from
# degree n >= 10 tries when RECOG.Form_GoingUpCycleBasis fails, before it
# falls back to the transpositions; below, these cost few nodes, and for
# Sp(4,3) no word of RECOG.Form_GoingUpCycleSeeds seems to work
RECOG.Form_GoingUpCycleRetries := 3;

# Step 5 of the GoingUp step for Sp and SU relative to a new basis of W, as
# proposed in the draft of [EHNPR] ('Constructing the enlarged group'),
# with m = n'/2 pairs, beta and eps as in the comment above
# RECOG.Form_RootElement:
#  - h = x x^g~ for x = a' z, z = v_U, and a' = a^(v_U^(m_U - 1)) acting on
#    the pivot pair, a from RECOG.Form_GoingUpCycleSeeds, such that the
#    characteristic polynomial of h on W is squarefree;
#  - e from RECOG.Form_IsotropicKrylovVector: the b_i = e h^(i-1),
#    1 <= i <= m, span a totally isotropic E, and y = e h^m;
#  - r = T(e - y, 1 / beta(y, e - y)) fixes b_2, ..., b_m and maps y to e,
#    so c = h r is the cycle b_1 -> b_2 -> ... -> b_m -> b_1 on E;
#  - a basis f_i of a totally isotropic complement F of E with
#    beta(b_i, f_j) = delta_ij: then f_i c = f_(i+1) + sum_k Z_(i,k-1) b_k
#    with Z_(k,i) = -eps Z_(i,k)^sigma, which a change
#    f_i -> f_i + sum_k S_ik b_k replaces by Z + S - C S C^-1, C the cyclic
#    shift; moving the sum along each cyclic diagonal of Z to its first row
#    or column leaves the radical part of c supported there, the product of
#    two transvections with centres in E; if p does not divide m, c^p is
#    the pair cycle relative to a suitable dual basis, as proposed in the
#    same draft, and needs no correction;
#  - this gives v_W relative to the basis (b_1, f_1, ..., b_m, f_m), and
#    the other standard generators are products of transvections with
#    centres among b_1, f_1, b_2, b_1 + b_2, b_1 - b_2, f_1 - f_2 and, for
#    x and y of SU, b_2 + alpha f_1.
# Each transvection of W costs O(n log q) nodes, so the step costs
# O(n log q) nodes instead of the Theta(n^2 log q) of the transpositions.
# <F> are the generators with memory standing for Y and g~, <RF> the root
# elements on them, <g> the matrix of g~ relative to the adapted basis,
# and <transvection>(w, lambda) the word for T(w, lambda), w a row of
# length d. Returns fail if no candidate works, else the record of
# RECOG.GoingUpStep.
RECOG.Form_GoingUpCycleBasis := function(std, F, RF, g, transvection)
  local f, d, n, nn, m, mU, names, Fw, Ystd, vpos, G, emb, J, q0, conj, form,
        eps, zm, cw, cm, gi, seed, xw, xm, hW, chi, e, hw, b, i, y, vv, lam,
        rW, c1, solver, f0, Gr, fv, next, X, Z, S, delta, a, sum, sv, k,
        half, Zp, mu, lamf, zt, w1, w2, pad, vW, basis, words, B1, F1, B2, F2,
        T, slam, sw, tau, x12, x21, om;

  f := std.f;
  d := std.d;
  n := std.n;
  nn := Minimum(2 * n - 2, d);
  m := nn / 2;
  mU := n / 2;
  names := RECOG.ClassicalStandardGeneratorNames(std.type);
  Fw := rec();
  for i in [1 .. Length(names)] do
    Fw.(names[i]) := F[i];
  od;
  G := F[Length(F)];
  Ystd := RECOG.ClassicalStandardGenerators(std.type, n, f);
  vpos := Position(names, "v");
  emb := M -> RECOG.GoingUpEmbed(M, d, f);
  J := RECOG.ClassicalForm(std.type, nn, f).gram;
  if std.type = "SU" then
    q0 := RootInt(Size(f));
    conj := v -> List(v, c -> c^q0);
  else
    q0 := Size(f);
    conj := v -> v;
  fi;
  form := {x, z} -> x * J * conj(z);
  eps := RF.eps;
  zm := emb(Ystd.v);
  cw := F[vpos]^(mU - 1);
  cm := emb(Ystd.v^(mU - 1));
  gi := g^-1;

  e := fail;
  for seed in RECOG.Form_GoingUpCycleSeeds do
    xw := seed(Fw)^cw * F[vpos];
    xm := cm^-1 * emb(seed(Ystd)) * cm * zm;
    hW := (xm * gi * xm * g){[1 .. nn]}{[1 .. nn]};
    chi := CharacteristicPolynomial(hW);
    if DegreeOfLaurentPolynomial(Gcd(chi, Derivative(chi))) = 0 then
      e := RECOG.Form_IsotropicKrylovVector(hW, J, f, chi, std.type);
      if e <> fail then
        break;
      fi;
    fi;
  od;
  if e = fail then
    Info(InfoRecog_ClassicalNatural, 3, "GoingUp: no cycle word");
    return fail;
  fi;
  hw := xw * xw^G;
  pad := w -> ImmutableVector(f, Concatenation(w,
                  ListWithIdenticalEntries(d - nn, Zero(f))));

  # the cycle c = h r on E
  b := [e];
  for i in [2 .. m] do
    Add(b, b[i - 1] * hW);
  od;
  y := b[m] * hW;
  vv := e - y;
  lam := form(y, vv)^-1;
  rW := IdentityMat(nn, f) + lam * TransposedMat([J * conj(vv)]) * [vv];
  c1 := hW * rW;
  Assert(1, ForAll([1 .. m], i -> b[i] * c1 = b[i mod m + 1]));

  # mu <> 0 with mu^sigma = -eps mu
  if std.type = "SU" then
    mu := PrimitiveRoot(f)^((q0 + 1) / 2);
  else
    mu := One(f);
  fi;

  # for p not dividing m, c' = c^p is the pair cycle: c^m - 1 maps W into
  # E and kills E, so c^(mp) = 1, and c' still cycles all of E. Relative to
  # e_i = e c'^(i-1) and f_i = f_1 c'^(i-1), beta(e_i, f_1) = delta_i1, the
  # Gram matrix G of the f_i is circulant, and f_i -> f_i - sum_j G_ij e_j/2
  # makes F totally isotropic and commutes with c'
  if m mod Characteristic(f) <> 0 then
    c1 := c1^Characteristic(f);
    b := [e];
    for i in [2 .. m] do
      Add(b, b[i - 1] * c1);
    od;
    solver := RECOG.GoingUpSolver(TransposedMat(List(b, x -> x * J)));
    fv := [conj(solver(IdentityMat(m, f)[1]))];
    for i in [2 .. m] do
      Add(fv, fv[i - 1] * c1);
    od;
    Gr := fv * J * TransposedMat(List(fv, conj));
    fv := List([1 .. m], j -> fv[j] - Gr[j] * b / 2);
    Assert(1, fv[m] * c1 = fv[1]
              and IsZero(fv * J * TransposedMat(List(fv, conj))));
    vW := (hw * transvection(pad(vv), lam))^Characteristic(f);
  else
    # f_i with beta(b_i, f_j) = delta_ij and beta(f_i, f_j) = 0
    solver := RECOG.GoingUpSolver(TransposedMat(List(b, x -> x * J)));
    f0 := List(IdentityMat(m, f), z -> conj(solver(z)));
    Gr := f0 * J * TransposedMat(List(f0, conj));
    fv := List([1 .. m], j -> f0[j] - Gr[j] * b / 2);

    # Z_(i,k) = beta(f_i c - f_(i+1), f_(k+1)), with Z_(k,i) =
    # -eps Z_(i,k)^sigma, and S moving the sum along each cyclic diagonal
    # (i, i + delta) to row 1 (and column 1 for its mirror diagonal
    # m - delta; to both for delta = m/2)
    next := i -> i mod m + 1;
    X := List([1 .. m], i -> (fv[i] * c1 - fv[next(i)]) * J);
    Z := X * TransposedMat(List([1 .. m], k -> conj(fv[next(k)])));
    Assert(1, ForAll([1 .. m], i -> ForAll([1 .. m],
                  k -> Z[k][i] = -eps * Z[i][k]^q0)));
    S := NullMat(m, m, f);
    for delta in [0 .. QuoInt(m, 2)] do
      a := List([1 .. m], i -> Z[i][(i + delta - 1) mod m + 1]);
      sum := Sum(a);
      half := 2 * delta = m;
      # on the diagonal m/2, S must be its own mirror: sv[2 + delta] =
      # -eps sv[2]^sigma, which this start achieves
      sv := [];
      sv[2] := Zero(f);
      if half then
        sum := Sum(a{[2 .. 1 + delta]});
        sv[2] := -(sum + eps * sum^q0) / 4;
        sum := Sum(a);
      fi;
      i := 2;
      for k in [1 .. m - 1] do
        sv[next(i)] := sv[i] + a[i];
        if half and i = 1 + delta then
          sv[next(i)] := sv[next(i)] - sum / 2;
        fi;
        i := next(i);
      od;
      for i in [1 .. m] do
        S[i][(i + delta - 1) mod m + 1] := sv[i];
        S[(i + delta - 1) mod m + 1][i] := -eps * sv[i]^q0;
      od;
    od;
    fv := List([1 .. m], i -> fv[i] + S[i] * b);
    X := List([1 .. m], i -> (fv[i] * c1 - fv[next(i)]) * J);
    Zp := TransposedMat(List([1 .. m], k -> conj(fv[next(k)])));
    Assert(1, ForAll((X * Zp){[2 .. m]}{[2 .. m]}, IsZero));
    Zp := X[1] * Zp;

    # T(w, lambda), w in E, adds lambda eps w^sigma w^T to Z; with mu and
    # lamf = 1 / (2 eps mu), the radical part of c is T(w_1, lamf)
    # T(w_2, -lamf)
    lamf := (2 * eps * mu)^-1;
    zt := ShallowCopy(Zp);
    zt[1] := zt[1] / 2;
    vW := hw * transvection(pad(vv), lam);
    if not IsZero(zt) then
      w1 := (IdentityMat(m, f)[1] + mu * zt) * b;
      w2 := (IdentityMat(m, f)[1] - mu * zt) * b;
      vW := transvection(pad(w2), lamf) * transvection(pad(w1), -lamf) * vW;
    fi;
  fi;

  basis := MutableCopyMat(IdentityMat(d, f));
  for i in [1 .. m] do
    basis[2 * i - 1] := pad(b[i]);
    basis[2 * i] := pad(fv[i]);
  od;

  # the generators on the first two pairs; T(b_2, .) = T(b_1, .)^vW. With
  # the transvections A(lambda) = T(f_1, lambda), B(lambda) = T(e_1,
  # lambda) on the first pair, A(l) B(-1/(eps l)) A(l) maps e_1 to l f_1
  # and f_1 to -e_1/l
  B1 := pad(b[1]);
  F1 := pad(fv[1]);
  B2 := pad(b[2]);
  F2 := pad(fv[2]);
  T := transvection;
  slam := l -> T(F1, l) * T(B1, -(eps * l)^-1) * T(F1, l);
  sw := slam(Ystd.s[1, 2]);
  tau := T(F1 - F2, RF.tau[2]) * T(B1 - B2, RF.tau[1]);
  words := rec( s := sw, t := T(F1, Ystd.t[1, 2]),
                delta := slam(Ystd.delta[1, 1] * Ystd.s[1, 2]) * sw^-1,
                u := tau * tau, v := vW );
  if std.type = "Sp" then
    words.x := T(B1 + B2, -One(f)) * T(B1, One(f)) * T(B1, One(f))^vW;
  else
    # x12(l): e_1 -> e_1 + l e_2, f_2 -> f_2 - l^sigma f_1, the product of
    # T(e_2 + alpha f_1, l1), T(e_2, -l1) and T(f_1, -mu), alpha = mu / l,
    # l1 = -l^(q0+1) / mu; x21(l) = x12(l)^u, and y is the torus element
    # x12(om) x21(-1/om) x12(om) of SL(<e_1, e_2>), om = y[1, 1], over the
    # one for om = 1
    x12 := l -> T(B2 + mu / l * F1, -l^(q0 + 1) / mu)
                * T(B1, l^(q0 + 1) / mu)^vW * T(F1, -mu);
    x21 := l -> x12(l)^words.u;
    om := Ystd.y[1, 1];
    words.x := x12(One(f));
    words.y := x12(om) * x21(-om^-1) * x12(om)
               * (words.x * x21(-One(f)) * words.x)^-1;
  fi;
  return rec( words := List(names, nm -> words.(nm)), basis := basis );
end;

# Step 5 of the GoingUp step ([EHNPR], 'Constructing the enlarged group'):
# the standard generators of CL(W), W = U + N, as words in the standard
# generators <Y> of CL(U) and g~, whose matrix relative to the adapted
# basis is <g>; for Sp and SU, q odd, by RECOG.Form_GoingUpCycleBasis
# relative to a new basis if possible. Otherwise relative to the first n'
# vectors of the adapted basis: they are those of CL(U) except the pair
# cycle v, which is v_W = tau_(m'-1) ... tau_m v_U, where tau_j swaps the
# pairs j and j+1. Each tau_j is a product of four transvections of W,
# which are conjugates of transvections of U. Returns the record of
# RECOG.Form_GoingUpCycleBasis, or fail, so that the step is repeated
# with a new doubling element (see RECOG.Form_GoingUpCycleRetries), or
# else the list of words, as elements with memory in generators standing
# for Y and g~, which the optional argument gives, as a list.
RECOG.Form_GoingUpNewGenerators := function(std, Y, R, g, opt...)
  local f, d, n, nn, form, norm, F, RF, e, gi, Ub, Upb, Npb, Wb, coeffs,
        withNorm, mapInU, intoU, toE1, transvection, vpos, tau, v, j, a, b,
        res;

  f := std.f;
  d := std.d;
  n := std.n;
  nn := Minimum(2 * n - 2, d);
  form := RECOG.ClassicalForm(std.type, d, f);
  norm := w -> RECOG.FormValue(form, w, w);
  if Length(opt) = 0 then
    F := GeneratorsWithMemory(ListWithIdenticalEntries(Length(Y) + 1, ()));
  else
    F := opt[1];
  fi;
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
  # 2c = nu - mu, resp. c + c^sigma = nu - mu with c = (nu - mu) RF.half
  # for SU; for Sp, all norms are 0
  withNorm := function(z, nu)
    local c;
    if not IsZero(z) and norm(z) = nu then
      return z;
    fi;
    z := ShallowCopy(z);
    z[n - 1] := Zero(f);
    z[n] := Zero(f);
    c := nu - norm(z);
    if IsBound(RF.half) then
      z[n] := c * RF.half;
    elif not IsZero(c) then
      z[n] := c / 2;
    fi;
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
  # T(e_1, lambda)^(h^-1) for h mapping w to e_1, which is kept for each w;
  # T(0, lambda) = 1
  toE1 := [[], []];
  transvection := function(w, lambda)
    local pos, h;
    if IsZero(w) then
      return F[1]^0;
    fi;
    pos := Position(toE1[1], w);
    if pos = fail then
      h := intoU(w);
      Add(toE1[1], w);
      Add(toE1[2], h.word * RECOG.Form_MapToStd(RF, h.vector{[1 .. n]}).word);
      pos := Length(toE1[1]);
    fi;
    h := toE1[2][pos];
    return h * RECOG.Form_RootElement(RF, "Le", 1, lambda) * h^-1;
  end;

  # a new doubling element is cheaper than the transpositions below; the
  # construction needs q odd and n' even
  if std.type in ["Sp", "SU"] and IsOddInt(Size(f)) and IsEvenInt(nn) then
    res := RECOG.Form_GoingUpCycleBasis(std, F, RF, g, transvection);
    if not IsBound(std.cycleRetries) then
      std.cycleRetries := 0;
    fi;
    if res <> fail then
      std.cycleRetries := 0;
      return res;
    elif n >= 10 and std.cycleRetries < RECOG.Form_GoingUpCycleRetries then
      std.cycleRetries := std.cycleRetries + 1;
      return fail;
    fi;
    std.cycleRetries := 0;
  fi;

  # tau_j = T(b, y) T(a, x) T(b, y) T(a, x), a = e_j - e_(j+1),
  # b = f_j - f_(j+1), with [x, y] = RF.tau, and for q even
  # tau_j = T(a + b, 1) T(a, 1) T(b, 1), a = e_j + e_(j+1),
  # b = f_j + f_(j+1) ([EHNPR], 'Constructing the enlarged group')
  vpos := Position(RECOG.ClassicalStandardGeneratorNames(std.type), "v");
  v := F[vpos];
  for j in [n / 2 .. QuoInt(nn, 2) - 1] do
    a := e[2 * j - 1] - e[2 * j + 1];
    b := e[2 * j] - e[2 * j + 2];
    if IsBound(RF.tau) then
      tau := transvection(b, RF.tau[2]) * transvection(a, RF.tau[1]);
      v := tau * tau * v;
    else
      v := transvection(a + b, One(f)) * transvection(a, One(f))
           * transvection(b, One(f)) * v;
    fi;
  od;
  res := F{[1 .. Length(Y)]};
  res[vpos] := v;
  return res;
end;

# The basis <bas> with its rows n+1, ..., d replaced by a standard basis of
# their span, for the multiple of the form of <G> of type <type> ("Sp", "SU"
# or an orthogonal type) for which the first <n> rows are a standard basis,
# of type "O+" for orthogonal groups, as at the end of the final descent of
# [EHNPR] ('Terminal groups and initial groups'). The last d-n rows of
# <bas> must span the orthogonal complement of the first n. For type "O",
# that multiple must lie in the square class of the form of
# RECOG.ClassicalInvariantForm.
RECOG.Form_CompleteStandardBasis := function(G, type, bas, n)
  local f, form, c;

  f := DefaultFieldOfMatrixGroup(G);
  form := RECOG.ClassicalInvariantForm(type,
              StripMemory(GeneratorsOfGroup(G)), f);
  c := RECOG.FormValue(form, bas[1], bas[2]);
  form.gram := form.gram / c;
  if IsBound(form.quad) then
    form.quad := form.quad / c;
  fi;
  Assert(1, RECOG.FormGram(form, bas{[1 .. n]})
            = RECOG.ClassicalStandardForm(RECOG.ClassicalPrefixType(type),
                                          n, f));
  bas := Concatenation(bas{[1 .. n]},
             RECOG.FormStandardBasis(form, bas{[n + 1 .. NrRows(bas)]}));
  ConvertToMatrixRep(bas, f);
  return bas;
end;
