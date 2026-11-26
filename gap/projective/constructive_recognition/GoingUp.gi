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

# A preimage z of <a> under the norm N: z -> z^(q0^k + 1) of the field
# K = F[x]/(<f>) of order q0^(2k) onto its subfield L of order q0^k, for
# F = GF(q0^2) with q0 odd, a <> 0 in L, and <f> irreducible of degree k,
# which is odd, with f^dagger = f; <f> and <a> are polynomials in the sense
# of RECOG.Pol.
# With q0^k - 1 = 2^S Q, Q odd: r = a^((Q+1)/2) has r^2 = a t, and t = a^Q
# lies in the Sylow 2-subgroup of L^*, which is generated by an element c
# of GF(q0), as k is odd. So t = c^j, and z = r c^(-j/2) for even j. For
# odd j, a is a non-square: then z = r c^((1-j)/2) / theta for theta in F
# with theta^(q0+1) = c, which is N(theta).
RECOG.Form_NormPreimage := function(F, f, a)
  local q0, k, Q, S, u, r, t, theta, c, j, i;

  q0 := RootInt(Size(F));
  k := Length(f) - 1;
  Q := q0^k - 1;
  S := 0;
  while IsEvenInt(Q) do
    Q := Q / 2;
    S := S + 1;
  od;
  u := RECOG.PolPowerMod(a, (Q - 1) / 2, f);
  r := RECOG.PolProductMod(u, a, f);
  t := RECOG.PolProductMod(r, u, f)[1];

  theta := PrimitiveRoot(F)^((q0 - 1) / 2^S);
  c := theta^(q0 + 1);
  j := 0;
  for i in [0 .. S - 1] do
    if not IsOne((t / c^j)^(2^(S - 1 - i))) then
      j := j + 2^i;
    fi;
  od;
  if IsEvenInt(j) then
    return r / c^(j / 2);
  fi;
  return r * c^((1 - j) / 2) / theta;
end;

# [u, v] in L = F[y]/(<g>) with u^2 + u v y + v^2 = a, for a <> 0 in L and
# <g> irreducible over <F> = GF(q), q odd, other than y - 2 and y + 2; <g>
# and <a> are polynomials in the sense of RECOG.Pol. That is N(u + v x) = a
# for the norm N of K = L[x]/(x^2 - y x + 1) to L, where 1/x = y - x is the
# conjugate of x. K is a field or L + L, and N is onto in both cases.
# With q^k - 1 = 2^S Q, Q odd, and b = a N(theta), where theta = 1 if a is
# a square of L and theta = x + c with a non-square norm c^2 + c y + 1
# otherwise: w = b^((Q-1)/2) has w^2 b = t in the Sylow 2-subgroup of L^*,
# and the Tonelli-Shanks loop makes t = 1. Then N(a w theta) = a.
# The loop needs an element of order 2^(i+1) if t has order 2^i: from F if
# 2^(i+1) divides q - 1, as for odd k, else from another power d^Q of a
# non-square d of L. An element of L is a square if and only if its norm
# to F is one, and that norm is a resultant. So there is one power with
# an exponent of the size of |L|, or two.
RECOG.Form_QuadraticNormPreimage := function(F, g, a)
  local q, k, one, mul, y, isSquare, enum, nonSquareNorm, c, b, d, Q, S, s0,
        order, w, t, i, M, z;

  q := Size(F);
  k := Length(g) - 1;
  one := g{[k + 1]};
  mul := {u, v} -> RECOG.PolProductMod(u, v, g);
  y := RECOG.PolMod(RECOG.Pol(F, [Zero(F), One(F)]), g);
  isSquare := u -> IsOne(RECOG.PolResultant(g, u)^((q - 1) / 2));

  # [c, N(x + c)] for the first c in L, in the order of the q-adic digits
  # of 1, 2, ..., with a non-square norm; for c in F that is a c with
  # g(-c - 1/c) (-c)^k a non-square of F
  enum := Enumerator(F);
  nonSquareNorm := function()
    local i, c, b;

    i := 0;
    repeat
      i := i + 1;
      c := RECOG.PolMod(RECOG.Pol(F, enum{1 + CoefficientsQadic(i, q)}), g);
      b := RECOG.PolSum(mul(RECOG.PolSum(y, c), c), one);
    until Length(b) > 0 and not isSquare(b);
    return [c, b];
  end;

  c := fail;
  b := a;
  if not isSquare(a) then
    d := nonSquareNorm();
    c := d[1];
    d := d[2];
    b := mul(a, d);
  fi;

  Q := q^k - 1;
  S := 0;
  while IsEvenInt(Q) do
    Q := Q / 2;
    S := S + 1;
  od;
  s0 := 0;
  while (q - 1) mod 2^(s0 + 1) = 0 do
    s0 := s0 + 1;
  od;
  # i for t of order 2^i
  order := function(t)
    local i;

    i := 0;
    while t <> one do
      t := mul(t, t);
      i := i + 1;
    od;
    return i;
  end;

  w := RECOG.PolPowerMod(b, (Q - 1) / 2, g);
  t := mul(mul(w, w), b);
  i := order(t);
  if i > 0 then
    # z of order 2^M
    if i < s0 then
      M := s0;
      z := PrimitiveRoot(F)^((q - 1) / 2^s0) * one;
    else
      if c = fail then
        d := nonSquareNorm()[2];
      fi;
      M := S;
      z := RECOG.PolPowerMod(d, Q, g);
    fi;
    while i > 0 do
      z := RECOG.PolPowerMod(z, 2^(M - i - 1), g);
      w := mul(w, z);
      z := mul(z, z);
      t := mul(t, z);
      M := i;
      i := order(t);
    od;
  fi;

  w := mul(a, w);
  if c = fail then
    return [w, g{[]}];
  fi;
  return [mul(w, c), w];
end;

# The polynomial p with p(x) p(1/x) = c N modulo <chi>, for c = 1 or c a
# non-square of <F> = GF(q), q odd, or fail. Here <chi> is squarefree and
# self-reciprocal, a polynomial in the sense of RECOG.Pol, and
# N = sum_k nu_k (x^k + x^-k) for the list <nu> of the nu_k, k >= 0.
# chi = (x - 1)^i (x + 1)^j x^m chi0(x + 1/x) with i, j <= 1, and N = n(y),
# y = x + 1/x, for a polynomial n. Modulo x - 1 and x + 1, p is a square
# root of n(2) resp. n(-2), which are made squares by c, if possible.
# Each irreducible factor g of chi0 of degree k stands for a factor
# x^k g(x + 1/x) of chi, irreducible or a product f f^dagger, and
# RECOG.Form_QuadraticNormPreimage gives p = u(y) + v(y) x modulo that in
# both cases. So the polynomial to factor has half the degree of chi, the
# pairs f, f^dagger need not be split, and the norm equations are solved
# in fields of order q^k, not q^(2k). The u and v are combined modulo chi0,
# and p is taken times x^(m-1), which has norm 1, as that is a polynomial
# in x.
RECOG.Form_ReciprocalNormRoot := function(F, chi, nu)
  local q, one, chi1, ends, eps, m, n, vals, squares, omega, p, chi0, mods,
        rems, g, a, uv, corr;

  q := Size(F);
  one := One(F);
  chi1 := chi;
  ends := [];
  for eps in [one, -one] do
    if IsZero(ValuePol(chi, eps)) then
      Add(ends, eps);
      chi1 := RECOG.PolQuotient(chi1, RECOG.Pol(F, [-eps, one]));
    fi;
  od;
  m := (Length(chi1) - 1) / 2;

  n := RECOG.PolOfReciprocalSum(
           RECOG.Pol(F, Concatenation([2 * nu[1]], nu{[2 .. Length(nu)]})));
  vals := List(ends, eps -> ValuePol(n, 2 * eps));
  squares := Set(vals, v -> v^((q - 1) / 2));
  if Length(squares) > 1 or Zero(F) in squares then
    return fail;
  elif squares = [-one] then
    omega := PrimitiveRoot(F);
    n := omega * n;
    vals := omega * vals;
  fi;

  if m = 0 then
    p := Zero(F) * chi{[1]};
  else
    chi0 := RECOG.PolOfReciprocalSum(chi1{[m + 1 .. 2 * m + 1]});
    n := RECOG.PolMod(n, chi0);
    mods := RECOG.PolFactorsSquarefree(F, chi0);
    rems := [];
    for g in mods do
      a := RECOG.PolMod(n, g);
      if Length(a) = 0 then
        return fail;
      fi;
      Add(rems, RECOG.Form_QuadraticNormPreimage(F, g, a));
    od;
    uv := RECOG.PolChineseRemainder(chi0, mods, rems);
    p := RECOG.PolSum(
             ShiftedCoeffs(RECOG.PolAtReciprocalSum(F, uv[2], m - 1), 1),
             RECOG.PolAtReciprocalSum(F, uv[1], m - 1));
  fi;

  # p + chi1 l with (p + chi1 l)(eps)^2 = n(2 eps), l of degree 0 or 1
  if Length(ends) > 0 then
    corr := List([1 .. Length(ends)],
                 i -> (RootFFE(F, vals[i], 2) - ValuePol(p, ends[i]))
                      / ValuePol(chi1, ends[i]));
    if Length(ends) = 2 then
      corr := [(corr[1] + corr[2]) / 2, (corr[1] - corr[2]) / 2];
    fi;
    corr := RECOG.Pol(F, corr);
    if Length(corr) > 0 then
      AddCoeffs(p, ProductCoeffs(chi1, corr));
    fi;
  fi;
  ShrinkRowVector(p);
  return p;
end;

# The polynomial p with p p^dagger = N modulo <chi>, for <F> = GF(q0^2), q0
# odd, a^dagger = a^sigma(1/x) with sigma: c -> c^q0 on the coefficients,
# chi = chi^dagger squarefree and N = N^dagger coprime to chi; <chi> and
# <N> are polynomials in the sense of RECOG.Pol. For a pair of irreducible
# factors f <> f^dagger of chi, p is N modulo f and 1 modulo f^dagger; for
# f = f^dagger it is from RECOG.Form_NormPreimage.
RECOG.Form_UnitaryNormRoot := function(F, chi, N)
  local q0, mods, rems, f, fs;

  q0 := RootInt(Size(F));
  mods := [];
  rems := [];
  for f in RECOG.PolFactorsSquarefree(F, chi) do
    if f in mods then
      continue;
    fi;
    fs := RECOG.Pol(F, Reversed(List(f, c -> c^q0)));
    fs := fs / fs[Length(fs)];
    Add(mods, f);
    if fs = f then
      Add(rems, [RECOG.Form_NormPreimage(F, f, RECOG.PolMod(N, f))]);
    else
      Add(rems, [RECOG.PolMod(N, f)]);
      Add(mods, fs);
      Add(rems, [fs{[Length(fs)]}]);
    fi;
  od;
  return RECOG.PolChineseRemainder(chi, mods, rems)[1];
end;

# A vector e of W = GF(q)^n, n = 2m, for the isometry <h> of the form
# beta(x, y) = x <J> y^(sigma T) of type <type>, "Sp", "SU", "O+" or "O"
# (n = 2m + 1; also n = 2m + 1 for "SU"), over <F> (sigma the identity,
# resp. c -> c^q0 for F = GF(q0^2)), with squarefree characteristic
# polynomial <chi>, such that beta(e, e h^j) = 0 for 0 <= j < k and
# beta(e, e h^k) <> 0, with k = m, resp. k = m - 1 for "O+", or fail. Then
# e, e h, ..., e h^(k-1) span a totally isotropic (singular) space, and for
# SU of even degree, where det h = 1, beta(e, e h^m) has trace 0.
# W is a cyclic F[h]-module: e = c p(h) for a cyclic vector c, and with
# phi(a) = beta(c, c a(h)), beta(e, e h^j) = phi(N x^j) for
# N = p p^dagger, a^dagger = a^sigma(x^-1), in A = F[x]/chi. The
# conditions on the self-adjoint N are linear over the fixed field of
# sigma, with a one-dimensional solution space <N0> in general, and the
# norm equation p p^dagger = N0 is solved by
# - RECOG.Form_ReciprocalNormRoot for Sp and O with q odd, which factors a
#   polynomial of half the degree of chi;
# - RECOG.Form_UnitaryNormRoot for SU with q odd, which factors chi;
# - a square root in A for q even, without any factorisation.
# In characteristic 2, h must not have the eigenvalue 1, and for "O+" the
# optional argument is the matrix of the quadratic form Q (as in
# RECOG.ClassicalForm). There N = nu_0 + sum_(k>0) nu_k (x^k + x^-k): the
# conditions for j > 0 are those above without the term phi(x^0) for nu_0,
# and for O+, Q(e) = nu_0 Q(c) + sum_(k>0) nu_k phi(x^k) replaces
# phi(N) = 0.
RECOG.Form_IsotropicKrylovVector := function(h, J, F, chi, type, quad...)
  local n, q0, conj, c, K, i, cJ, args, coeffs, top, e, form;

  n := NrRows(h);
  if type in ["O+", "Sp"] and IsEvenInt(Size(F))
     and IsZero(Value(chi, One(F))) then
    return fail;
  fi;
  if type = "SU" then
    q0 := RootInt(Size(F));
    conj := v -> List(v, y -> y^q0);
  else
    conj := v -> v;
  fi;

  repeat
    c := Random(F^n);
    K := [c];
    for i in [1 .. n] do
      Add(K, K[i] * h);
    od;
  until RankMat(K{[1 .. n]}) = n;
  cJ := c * J;
  args := [List(K, y -> cJ * conj(y)), F, chi, type];
  if Length(quad) > 0 then
    Add(args, c * quad[1] * c);
  fi;
  coeffs := CallFuncList(RECOG.Form_IsotropicKrylovPolynomial, args);
  if coeffs = fail then
    return fail;
  fi;

  # e = c p(h), from the vectors c h^i
  e := Sum([1 .. Length(coeffs)], i -> coeffs[i] * K[i]);
  top := QuoInt(n, 2);
  if type = "O+" then
    top := top - 1;
  fi;
  form := {y, z} -> y * J * conj(z);
  Assert(1, ForAll([0 .. top - 1], j -> IsZero(form(e, e * h^j)))
            and not IsZero(form(e, e * h^top)));
  return e;
end;

# The coefficients of the polynomial p of RECOG.Form_IsotropicKrylovVector,
# lowest degree first, or fail: <phi> is the list of the beta(c, c h^i),
# 0 <= i <= n, for a cyclic vector c of h, which gives n, and <F>, <chi>
# and <type> are as there. In characteristic 2, for "Sp" and "O+", chi
# must not have the root 1, and for "O+" the optional argument is Q(c).
RECOG.Form_IsotropicKrylovPolynomial := function(phi, F, chi, type, Qc...)
  local n, m, q, q0, ph, F0, omega, coords, M, row, k, j, nu, cands, top,
        xi, N, a, even;

  n := Length(phi) - 1;
  m := n / 2;
  if type = "O" then
    # as "O+" with one more unknown and condition
    m := (n + 1) / 2;
    type := "O+";
  elif type = "SU" and IsOddInt(n) then
    # the solution space has dimension 2 in general
    m := (n - 1) / 2;
  fi;
  q := Size(F);
  even := type in ["O+", "Sp"] and IsEvenInt(q);
  q0 := q;
  if type = "SU" then
    q0 := RootInt(q);
  fi;

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
    if IsOddInt(n) then
      cands := Concatenation(cands, List(Combinations(cands, 2), Sum));
    fi;
  elif type = "O+" then
    # phi(N x^j) = 0 for 0 <= j < m - 1; the value at m - 1 is tested below
    M := List([0 .. m - 1], k -> List([0 .. m - 2],
                                      j -> ph(k + j) + ph(j - k)));
    if even then
      for j in [1 .. m - 2] do
        M[1][j + 1] := ph(j);
      od;
      for k in [1 .. m - 1] do
        M[k + 1][1] := ph(k);
      od;
      M[1][1] := Qc[1];
    fi;
    cands := NullspaceMat(M);
    if Length(cands) <> 1 then
      return fail;
    fi;
    cands := [Concatenation(cands[1], [Zero(F)])];
  else
    M := List([0 .. m - 1], k -> List([1 .. m - 1],
                                      j -> ph(k + j) + ph(j - k)));
    if even then
      for j in [1 .. m - 1] do
        M[1][j] := ph(j);
      od;
    fi;
    cands := NullspaceMat(M);
    if Length(cands) <> 1 then
      return fail;
    fi;
    cands := [Concatenation(cands[1], [Zero(F)])];
  fi;

  # a nu with N <> 0 and phi(N x^top) <> 0, top = m resp. m - 1 for "O+",
  # and p with p p^dagger = N
  top := m;
  if type = "O+" then
    top := m - 1;
  fi;
  chi := RECOG.Pol(F, CoefficientsOfUnivariatePolynomial(chi));
  for nu in cands do
    if even then
      a := nu[1] * ph(top) + Sum([1 .. m], k -> nu[k + 1] * (ph(k + top)
                                                             + ph(top - k)));
    else
      a := Sum([0 .. m], k -> nu[k + 1]^q0 * ph(k + top)
                              + nu[k + 1] * ph(top - k));
    fi;
    if IsZero(a) then
      continue;
    elif type <> "SU" and IsOddInt(q) then
      return RECOG.Form_ReciprocalNormRoot(F, chi, nu);
    fi;

    # N = x^-m sum_k (nu_k x^(m+k) + nu_k^sigma x^(m-k)) modulo chi
    N := ListWithIdenticalEntries(2 * m + 1, Zero(F));
    for k in [0 .. m] do
      N[m + 1 + k] := nu[k + 1];
      N[m + 1 - k] := N[m + 1 - k] + nu[k + 1]^q0;
    od;
    if even then
      N[m + 1] := nu[1];
    fi;
    xi := -chi{[2 .. n + 1]} / chi[1];
    N := RECOG.PolProductMod(RECOG.Pol(F, N), RECOG.PolPowerMod(xi, m, chi),
                             chi);
    # for odd n, the solution space gives no unit by itself
    if Length(N) = 0 or (IsOddInt(n) and type = "SU"
                         and Length(GcdCoeffs(N, chi)) > 1) then
      continue;
    elif IsEvenInt(q) then
      # the square root of N is self-adjoint, as N is
      return RECOG.PolSquareRootMod(F, N, chi);
    fi;
    return RECOG.Form_UnitaryNormRoot(F, chi, N);
  od;
  return fail;
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
# with m = [n'/2] pairs, beta and eps as in the comment above
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
#    two transvections with centres in E (three in characteristic 2); if p
#    does not divide m, c^p is the pair cycle relative to a suitable dual
#    basis, as proposed in the same draft, and needs no correction;
#  - this gives v_W relative to the basis (b_1, f_1, ..., b_m, f_m), and
#    the other standard generators are products of transvections with
#    centres among b_1, f_1, b_2, b_1 + b_2, b_1 - b_2, f_1 - f_2 and, for
#    x and y of SU, b_2 + alpha f_1.
# For SU of odd degree, W = V, E = <b_1, ..., b_m> is maximal totally
# isotropic, D = <b_2, ..., b_m>, c0 = beta(e, y) need not have trace 0,
# and <D, e, y>^perp = D + <a> with a anisotropic. With t in <a> of norm
# -(c0 + c0^sigma), the unitary Siegel transformation
# rho(e + (c0/c0^sigma) y + t, (y - e)/c0^sigma, 1/c0) of
# RECOG.SU_GoingUpNewGenerators fixes D and maps y to e, so c = h rho
# cycles E. Then a c = a + psi + tau e with psi in E, and for a2 = a + psi'
# with a2 c = a2 + tau e, rho(e, mu a2, .) with mu^sigma beta(a2, a2) =
# -tau makes c fix a2. The construction above runs in a2^perp, and x and
# y are those of odd degree, with w_1 = a2 scaled to norm 1.
# Each transvection of W costs O(n log q) nodes, so the step costs
# O(n log q) nodes instead of the Theta(n^2 log q) of the transpositions.
# <F> are the generators with memory standing for Y and g~, <RF> the root
# elements on them, <g> the matrix of g~ relative to the adapted basis,
# and <transvection>(w, lambda) the word for T(w, lambda), w a row of
# length d. For SU of odd degree, the optional argument is the function
# (p, z, lam) -> rho(p, z, lam) of RECOG.Form_GoingUpNewGenerators. Returns
# fail if no candidate works, else the record of RECOG.GoingUpStep.
RECOG.Form_GoingUpCycleBasis := function(std, F, RF, g, transvection, opt...)
  local f, d, n, nn, m, mU, names, Fw, Ystd, vpos, G, emb, J, q0, conj, form,
        eps, zm, cw, cm, gi, seed, xw, xm, hW, chi, e, hw, b, i, y, vv, lam,
        rW, c1, solver, f0, Gr, fv, next, X, Z, S, delta, a, sum, sv, k,
        half, Zp, mu, lamf, zt, w1, w2, pad, vW, basis, words, B1, F1, B2, F2,
        T, slam, sw, tau, x12, x21, om, p, halfGram, Kb, R, Bm, r1, al, odd,
        siegel, rho, c0, D, K, a0, t, uu, ww, kw, th, CM, sol, a2, lam2, wX,
        rows, unit, gam, alp, A, aa, Xp;

  f := std.f;
  p := Characteristic(f);
  d := std.d;
  n := std.n;
  nn := Minimum(2 * n - 2, d);
  odd := IsOddInt(nn);
  if odd then
    siegel := opt[1];
  fi;
  m := QuoInt(nn, 2);
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
  if odd then
    rho := function(u, w, l)
      return List(IdentityMat(nn, f), x -> x + form(x, w) * u
                      - form(x, u) * w + l * form(x, u) * u);
    end;
    c0 := form(e, y);
    D := b{[2 .. m]};
    K := NullspaceMat(J * TransposedMat(List(Concatenation(D, [e, y]),
                                             conj)));
    a0 := BaseSteinitzVectors(K, D).factorspace[1];
    t := Zero(e);
    if not IsZero(c0 + c0^q0) then
      t := RootFFE(f, -(c0 + c0^q0) / form(a0, a0), q0 + 1) * a0;
    fi;
    uu := e + c0 / c0^q0 * y + t;
    ww := (y - e) / c0^q0;
    c1 := hW * rho(uu, ww, c0^-1);
    kw := hw * siegel(pad(uu), pad(ww), c0^-1);

    # a2 = a0 + psi' and tau from theta = a0 c - a0 = psi' (c - 1) + tau e
    th := SolutionMat(b, a0 * c1 - a0);
    if th = fail then
      return fail;
    fi;
    CM := List(b, x -> SolutionMat(b, x * c1));
    sol := SolutionMat(Concatenation(CM - IdentityMat(m, f),
                                     [IdentityMat(m, f)[1]]), -th);
    if sol = fail then
      return fail;
    fi;
    a2 := a0 + sol{[1 .. m]} * b;
    if not IsZero(sol[m + 1]) then
      ww := (sol[m + 1] / form(a2, a2))^q0 * a2;
      lam2 := -form(ww, ww) * RF.half;
      c1 := c1 * rho(e, ww, lam2);
      kw := kw * siegel(pad(e), pad(ww), lam2);
    fi;
    Assert(1, a2 * c1 = a2);
    wX := RootFFE(f, form(a2, a2)^-1, q0 + 1) * a2;
  else
    vv := e - y;
    lam := form(y, vv)^-1;
    rW := IdentityMat(nn, f) + lam * TransposedMat([J * conj(vv)]) * [vv];
    c1 := hW * rW;
    kw := hw * transvection(pad(vv), lam);
  fi;
  Assert(1, ForAll([1 .. m], i -> b[i] * c1 = b[i mod m + 1]));

  # the conditions beta(b_i, x) = z_i on x^sigma, and beta(a2, x) = 0 for
  # odd degree
  rows := function()
    local r;
    r := List(b, x -> x * J);
    if odd then
      Add(r, a2 * J);
    fi;
    return TransposedMat(r);
  end;
  unit := j -> IdentityMat(m + nn mod 2, f)[j];

  # mu <> 0 with mu^sigma = -eps mu
  if std.type = "SU" and p > 2 then
    mu := PrimitiveRoot(f)^((q0 + 1) / 2);
  else
    mu := One(f);
  fi;

  # S with S_il + eps S_li^sigma = G_il for the Gram matrix G of vectors
  # f_i dual to the b_i, so that the f_i - sum_l S_il b_l are totally
  # isotropic; S is circulant if G is and m is odd. G/2 for q odd, h G with
  # h of trace 1 for SU, and for Sp in characteristic 2 the entries of G on
  # the cyclic diagonals 1, ..., (m-1)/2 and half of the diagonal m/2
  halfGram := function(Gr)
    local S, i, l, dl;
    if p > 2 then
      return Gr / 2;
    elif std.type = "SU" then
      return RF.half * Gr;
    fi;
    S := NullMat(m, m, f);
    for i in [1 .. m] do
      for l in [1 .. m] do
        dl := (l - i) mod m;
        if (0 < dl and 2 * dl < m) or (2 * dl = m and i < l) then
          S[i][l] := Gr[i][l];
        fi;
      od;
    od;
    return S;
  end;

  # for p not dividing m, c' = c^p is the pair cycle: c^m - 1 maps W into
  # E and kills E, so c^(mp) = 1, and c' still cycles all of E. Relative to
  # e_i = e c'^(i-1) and f_i = f_1 c'^(i-1), beta(e_i, f_1) = delta_i1, the
  # Gram matrix G of the f_i is circulant, and f_i -> f_i - sum_j S_ij e_j
  # for S of halfGram makes F totally isotropic and commutes with c'
  if m mod p <> 0 then
    c1 := c1^Characteristic(f);
    b := [e];
    for i in [2 .. m] do
      Add(b, b[i - 1] * c1);
    od;
    solver := RECOG.GoingUpSolver(rows());
    fv := [conj(solver(unit(1)))];
    for i in [2 .. m] do
      Add(fv, fv[i - 1] * c1);
    od;
    Gr := halfGram(fv * J * TransposedMat(List(fv, conj)));
    fv := List([1 .. m], j -> fv[j] - Gr[j] * b);
    Assert(1, fv[m] * c1 = fv[1]
              and IsZero(fv * J * TransposedMat(List(fv, conj))));
    vW := kw^p;
  else
    # f_i with beta(b_i, f_j) = delta_ij and beta(f_i, f_j) = 0
    solver := RECOG.GoingUpSolver(rows());
    f0 := List([1 .. m], j -> conj(solver(unit(j))));
    Gr := halfGram(f0 * J * TransposedMat(List(f0, conj)));
    fv := List([1 .. m], j -> f0[j] - Gr[j] * b);

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
      # -eps sv[2]^sigma, which this start achieves. In characteristic 2,
      # the first half of that diagonal is summed and the second half is
      # its mirror, which leaves the remainder at (1, 1 + delta) and
      # (1 + delta, 1).
      sv := [];
      sv[2] := Zero(f);
      if half and p = 2 then
        for i in [2 .. delta] do
          sv[i + 1] := sv[i] + a[i];
        od;
        for i in [2 .. delta + 1] do
          sv[(i + delta - 1) mod m + 1] := -eps * sv[i]^q0;
        od;
        for i in [1 .. m] do
          S[i][(i + delta - 1) mod m + 1] := sv[i];
        od;
        continue;
      fi;
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
    vW := kw;
    if p > 2 then
      lamf := (2 * eps * mu)^-1;
      zt := ShallowCopy(Zp);
      zt[1] := zt[1] / 2;
      if not IsZero(zt) then
        w1 := (IdentityMat(m, f)[1] + mu * zt) * b;
        w2 := (IdentityMat(m, f)[1] - mu * zt) * b;
        vW := transvection(pad(w2), lamf) * transvection(pad(w1), -lamf) * vW;
      fi;
    else
      # in characteristic 2, R = v c^-1 for the pair cycle v relative to
      # (b_i, f_i) fixes E pointwise, and f_i R = f_i + sum_k B_ik b_k with
      # B supported on its first row r and column. T(w, lambda),
      # w = sum w_k b_k, has B = lambda (w^sigma)^T w. With z = r without
      # its first entry: for Sp, B is that of T(b_1 + z, 1) T(b_1, r_1 + 1)
      # T(z, 1); for SU, of T(b_1 + al z, l) T(b_1 + al^sigma z, l)
      # T(b_1, r_1) with l = 1 / (al + al^sigma), al not in GF(q0)
      Kb := Concatenation(List([1 .. m], i -> [b[i], fv[i]]));
      if odd then
        Add(Kb, wX);
      fi;
      R := Kb^-1 * RECOG.ClassicalStandardGenerators(std.type, nn, f).v * Kb
           * c1^-1;
      Bm := List([1 .. m], i -> List([1 .. m],
                k -> form(fv[i] * R - fv[i], fv[k])));
      Assert(1, ForAll(b, x -> x * R = x)
                and ForAll(Bm{[2 .. m]}{[2 .. m]}, IsZero));
      zt := ShallowCopy(Bm[1]);
      r1 := zt[1];
      zt[1] := Zero(f);
      if IsZero(zt) then
        if not IsZero(r1) then
          vW := transvection(pad(b[1]), r1) * vW;
        fi;
      elif std.type = "Sp" then
        vW := transvection(pad(b[1] + zt * b), One(f))
              * transvection(pad(zt * b), One(f)) * vW;
        if not IsOne(r1) then
          vW := transvection(pad(b[1]), r1 + One(f)) * vW;
        fi;
      else
        al := PrimitiveRoot(f);
        lamf := (al + al^q0)^-1;
        vW := transvection(pad(b[1] + al * zt * b), lamf)
              * transvection(pad(b[1] + al^q0 * zt * b), lamf) * vW;
        if not IsZero(r1) then
          vW := transvection(pad(b[1]), r1) * vW;
        fi;
      fi;
    fi;
  fi;

  basis := MutableCopyMat(IdentityMat(d, f));
  for i in [1 .. m] do
    basis[2 * i - 1] := pad(b[i]);
    basis[2 * i] := pad(fv[i]);
  od;
  if odd then
    basis[nn] := pad(wX);
  fi;

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
  # the swap u of the first two pairs, as in the transpositions of
  # RECOG.Form_GoingUpNewGenerators
  if IsBound(RF.tau) then
    tau := T(F1 - F2, RF.tau[2]) * T(B1 - B2, RF.tau[1]);
    tau := tau * tau;
  else
    tau := T(B1 + B2 + F1 + F2, One(f)) * T(B1 + B2, One(f))
           * T(F1 + F2, One(f));
  fi;
  words := rec( s := sw, t := T(F1, Ystd.t[1, 2]),
                delta := slam(Ystd.delta[1, 1] * Ystd.s[1, 2]) * sw^-1,
                u := tau, v := vW );
  if odd then
    # x and y of odd degree, as in RECOG.SU_GoingUpNewGenerators
    gam := PrimitiveRoot(f);
    alp := RECOG.UnitaryAlpha(f);
    A := alp * gam;
    aa := RootFFE(f, -(A + A^q0), q0 + 1);
    Xp := pad(wX);
    words.x := siegel(F1, -Xp, -RF.half);
    words.y := siegel(F1, aa * Xp, A) * siegel(B1, -(aa / A) * Xp, A^-q0)
               * siegel(F1, aa * A^(q0 - 1) * Xp, A) * sw^-1;
  elif std.type = "Sp" then
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
# basis is <g>; for Sp and SU by RECOG.Form_GoingUpCycleBasis relative to
# a new basis if possible. Otherwise relative to the first n'
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
        withNorm, mapInU, act, intoU, toE1, toStd, transvection, siegel, SP,
        cU, vpos, tau, v, j, a, b, res;

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

  # an element of CL(U), as a word in F and its matrix on U, mapping y to
  # z, both nonzero in U and of the same norm
  mapInU := function(y, z)
    local a, b;
    a := RECOG.Form_MapToStd(RF, y{[1 .. n]});
    b := RECOG.Form_MapToStd(RF, z{[1 .. n]});
    return rec( word := a.word * b.word^-1, mat := a.mat * b.mat^-1 );
  end;

  # the image of w under the product of the matrices in <steps>, each on V
  # or on U
  act := function(steps, w)
    local M;
    for M in steps do
      if NrRows(M) = d then
        w := w * M;
      else
        w := Concatenation(w{[1 .. n]} * M, w{[n + 1 .. d]});
      fi;
    od;
    return w;
  end;

  # A word h in Y and g~, its matrix as a list of factors for act, and the
  # vector wh in U, for nonzero w in W. Write
  # w = u' + x' with u' in U', x' in N'. Since U' projects onto N, the
  # vectors of U' with the projection to N of -x' are a coset of
  # U meet U', which contains a vector u'' of the norm of u'. An element of
  # CL(U') = CL(U)^g~ mapping u' to u'' fixes N' and maps w into U. If
  # u' = 0, the same with the roles of U, N and U', N' exchanged first maps
  # w into U'.
  intoU := function(w)
    local c, u, x, z, k, h;

    if IsZero(w{[n + 1 .. d]}) then
      return rec( word := F[1]^0, vector := w, steps := [] );
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
      return rec( word := k.word * h.word, vector := h.vector,
                  steps := Concatenation([k.mat], h.steps) );
    fi;

    u := c{[1 .. n]} * Upb;
    x := c{[n + 1 .. nn]} * Npb;
    z := SolutionMat(Upb{[1 .. n]}{[n + 1 .. nn]}, -x{[n + 1 .. nn]}) * Upb;
    z := withNorm(z, norm(u));
    k := mapInU(u * gi, z * gi);
    h := F[Length(F)]^-1 * k.word * F[Length(F)];
    Assert(1, IsZero((z + x){[n + 1 .. d]}));
    return rec( word := h, vector := z + x, steps := [gi, k.mat, g] );
  end;

  # the transvection T(w, lambda) of W, w isotropic, as
  # T(e_1, lambda)^(h^-1) for h mapping w to e_1, which is kept for each w
  # with its factors for act; T(0, lambda) = 1
  toE1 := [[], [], []];
  toStd := function(w)
    local pos, h, s;
    pos := Position(toE1[1], w);
    if pos = fail then
      h := intoU(w);
      s := RECOG.Form_MapToStd(RF, h.vector{[1 .. n]});
      Add(toE1[1], w);
      Add(toE1[2], h.word * s.word);
      Add(toE1[3], Concatenation(h.steps, [s.mat]));
      pos := Length(toE1[1]);
    fi;
    return pos;
  end;
  transvection := function(w, lambda)
    local h;
    if IsZero(w) then
      return F[1]^0;
    fi;
    h := toE1[2][toStd(w)];
    return h * RECOG.Form_RootElement(RF, "Le", 1, lambda) * h^-1;
  end;

  # for SU of odd degree, W = V: the unitary Siegel transformation
  # rho(p, z, lam) of SU/GoingUp.gi for isotropic p and z orthogonal to p,
  # as the conjugate of rho(e_m, z', lam') by h^-1, h mapping p to e_1 and
  # then by c = v^(m_U - 1) to e_m: z h = z' + kappa e_m with z' in A + N,
  # and lam' = lam + kappa^q0 - kappa
  siegel := fail;
  if std.type = "SU" and IsOddInt(nn) then
    SP := RECOG.SU_GoingUpSiegel(std, F, RF, g);
    cU := RECOG.ClassicalStandardGenerators("SU", n, f).v^(n / 2 - 1);
    siegel := function(p, z, lam)
      local pos, h, kap, q0;
      q0 := RootInt(Size(f));
      pos := toStd(p);
      h := toE1[2][pos] * SP.c;
      z := ShallowCopy(act(Concatenation(toE1[3][pos], [cU]), z));
      Assert(1, IsZero(z[n]));
      kap := z[n - 1];
      z[n - 1] := Zero(f);
      return h * SP.siegelP(n - 1, z, lam + kap^q0 - kap) * h^-1;
    end;
  fi;

  # a new doubling element is cheaper than the transpositions below
  if std.type in ["Sp", "SU"] then
    res := RECOG.Form_GoingUpCycleBasis(std, F, RF, g, transvection, siegel);
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
