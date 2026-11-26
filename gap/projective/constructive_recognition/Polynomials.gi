#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
##
##  Univariate polynomials over a finite field F as lists of coefficients,
##  lowest degree first, without trailing zeros, the zero polynomial being
##  the empty list. The lists are mutable and compressed if |F| <= 256: the
##  kernel then does the arithmetic, which is 10 to 100 times faster than
##  that of polynomial objects (`mod`, `Gcd`, `GcdRepresentation`). A product
##  of a compressed list with a plain one is plain, so every list entering
##  a computation comes from RECOG.Pol.
##
#############################################################################

# The polynomial with the coefficients <c> over <F>
RECOG.Pol := function(F, c)
  c := ShallowCopy(c);
  ConvertToVectorRep(c, Size(F));
  ShrinkRowVector(c);
  return c;
end;

# The remainder of <u> modulo <f>
RECOG.PolMod := function(u, f)
  if Length(u) < Length(f) then
    return u;
  fi;
  u := ShallowCopy(u);
  ReduceCoeffs(u, f);
  ShrinkRowVector(u);
  return u;
end;

# The sum of <u> and <v>
RECOG.PolSum := function(u, v)
  if Length(u) < Length(v) then
    return RECOG.PolSum(v, u);
  elif Length(v) = 0 then
    return u;
  fi;
  u := ShallowCopy(u);
  AddCoeffs(u, v);
  ShrinkRowVector(u);
  return u;
end;

# The product of <u> and <v> modulo <f>
RECOG.PolProductMod := function(u, v, f)
  local w;

  if Length(u) = 0 or Length(v) = 0 then
    return f{[]};
  fi;
  w := ProductCoeffs(u, v);
  ReduceCoeffs(w, f);
  ShrinkRowVector(w);
  return w;
end;

# The power <u>^<e> modulo <f>, for e >= 0 and f of positive degree
RECOG.PolPowerMod := function(u, e, f)
  if e = 0 then
    return f{[Length(f)]} / f[Length(f)];
  elif Length(u) = 0 then
    return u;
  fi;
  u := ShallowCopy(PowerModCoeffs(u, e, f));
  ShrinkRowVector(u);
  return u;
end;

# The quotient of <u> by its divisor <f>
RECOG.PolQuotient := function(u, f)
  u := QuotRemCoeffs(ShallowCopy(u), f)[1];
  ShrinkRowVector(u);
  return u;
end;

# The inverse of <u> modulo <f>, or fail if they are not coprime, by the
# extended Euclidean algorithm
RECOG.PolInverseMod := function(u, f)
  local r0, r1, t0, t1, qr, t2;

  r0 := f;
  r1 := RECOG.PolMod(u, f);
  t1 := f{[Length(f)]} / f[Length(f)];
  t0 := ZeroMutable(t1);
  while Length(r1) > 1 do
    qr := QuotRemCoeffs(ShallowCopy(r0), r1);
    ShrinkRowVector(qr[2]);
    t2 := ShallowCopy(t0);
    AddCoeffs(t2, ProductCoeffs(qr[1], t1), -One(f[1]));
    r0 := r1;
    r1 := qr[2];
    t0 := t1;
    t1 := t2;
  od;
  if Length(r1) = 0 then
    return fail;
  fi;
  t1 := t1 / r1[1];
  ShrinkRowVector(t1);
  return t1;
end;

# The resultant of <f> and <g>, both nonzero: for monic f the product of
# the g(a) over the roots a of f, which is the norm of g in F[x]/(f)
RECOG.PolResultant := function(f, g)
  local res, m, n, r;

  res := f[1]^0;
  while Length(g) > 1 do
    m := Length(f) - 1;
    n := Length(g) - 1;
    r := RECOG.PolMod(f, g);
    if Length(r) = 0 then
      return 0 * res;
    fi;
    # Res(f, g) = (-1)^(m n) lc(g)^(m - deg r) Res(g, r)
    res := res * g[n + 1]^(m - Length(r) + 1);
    if IsOddInt(m * n) then
      res := -res;
    fi;
    f := g;
    g := r;
  od;
  return res * g[1]^(Length(f) - 1);
end;

# For pairwise coprime monic polynomials <mods> with product <f> and lists
# rems[i] of the same length k, the k polynomials of degree less than deg f
# of which the j-th is congruent to rems[i][j] modulo mods[i]
RECOG.PolChineseRemainder := function(f, mods, rems)
  local n, res, i, cofactor, inv, r, w;

  n := Length(f) - 1;
  res := List(rems[1], r -> ZeroMutable(f{[1 .. n]}));
  for i in [1 .. Length(mods)] do
    cofactor := RECOG.PolQuotient(f, mods[i]);
    inv := RECOG.PolInverseMod(cofactor, mods[i]);
    for r in [1 .. Length(res)] do
      w := RECOG.PolProductMod(rems[i][r], inv, mods[i]);
      if Length(w) > 0 then
        AddCoeffs(res[r], ProductCoeffs(cofactor, w));
      fi;
    od;
  od;
  for r in res do
    ShrinkRowVector(r);
  od;
  return res;
end;

# The polynomial s with s(x + 1/x) = c_0 + sum_(j>0) c_j (x^j + x^-j) for
# the polynomial <c> with the coefficients c_j: x^j + x^-j is D_j(x + 1/x)
# with D_0 = 2, D_1 = y and D_(j+1) = y D_j - D_(j-1)
RECOG.PolOfReciprocalSum := function(c)
  local n, one, s, d0, d1, d2, j;

  n := Length(c);
  if n <= 1 then
    return c;
  fi;
  one := c[n]^0;
  s := c{[1]};
  d0 := 2 * c{[n]} / c[n];
  d1 := ShiftedCoeffs(c{[n]} / c[n], 1);
  for j in [1 .. n - 1] do
    AddCoeffs(s, d1, c[j + 1]);
    d2 := ShiftedCoeffs(d1, 1);
    AddCoeffs(d2, d0, -one);
    d0 := d1;
    d1 := d2;
  od;
  ShrinkRowVector(s);
  return s;
end;

# The polynomial x^D s(x + 1/x) = sum_j s_j x^(D-j) (x^2 + 1)^j for the
# polynomial <s> of degree at most <D> over <F>, as a list of length
# 2 D + 1, by Horner's rule
RECOG.PolAtReciprocalSum := function(F, s, D)
  local d, p, p2, j;

  d := Length(s) - 1;
  if d < 0 then
    p := ListWithIdenticalEntries(2 * D + 1, Zero(F));
    ConvertToVectorRep(p, Size(F));
    return p;
  fi;
  p := s{[d + 1]};
  for j in [d - 1, d - 2 .. 0] do
    p2 := ShiftedCoeffs(p, 2);
    AddCoeffs(p2, p);
    p := p2;
    p[d - j + 1] := p[d - j + 1] + s[j + 1];
  od;
  p := ShiftedCoeffs(p, D - d);
  PadCoeffs(p, 2 * D + 1);
  return p;
end;

# The square root of <u> modulo the squarefree polynomial <f> over <F>, of
# characteristic 2. With ' for the square roots of the coefficients,
# f = C(x^2) + x D(x^2) gives sqrt(x) = C' / D' modulo f, and
# u = A(x^2) + x B(x^2) has the square root A' + sqrt(x) B'
RECOG.PolSquareRootMod := function(F, u, f)
  local halves, c, a;

  # [A', B']
  halves := function(u)
    u := List(u, c -> RECOG.SqrtFFE2(c, Size(F)));
    return [RECOG.Pol(F, u{[1, 3 .. 2 * QuoInt(Length(u) + 1, 2) - 1]}),
            RECOG.Pol(F, u{[2, 4 .. 2 * QuoInt(Length(u), 2)]})];
  end;
  c := halves(f);
  a := halves(u);
  c := RECOG.PolProductMod(c[1], RECOG.PolInverseMod(c[2], f), f);
  return RECOG.PolSum(a[1], RECOG.PolProductMod(a[2], c, f));
end;

# The matrix of the Frobenius map u -> u^q of F[x]/(<f>), q = |F|, for <f>
# monic: its rows are the x^(q i) modulo f, 0 <= i < deg f, as lists of
# length deg f. A shift by q costs q elimination steps, a product with x^q
# about deg f.
RECOG.PolFrobeniusMatrix := function(F, f)
  local q, n, w, rows, xq, i;

  q := Size(F);
  n := Length(f) - 1;
  w := f{[n + 1]};
  PadCoeffs(w, n);
  rows := [w];
  if q > n then
    xq := RECOG.PolPowerMod(RECOG.Pol(F, [Zero(F), One(F)]), q, f);
  fi;
  for i in [2 .. n] do
    if q > n then
      w := ProductCoeffs(w, xq);
    else
      w := ShiftedCoeffs(w, q);
    fi;
    ReduceCoeffs(w, f);
    PadCoeffs(w, n);
    if Length(w) > n then
      w := w{[1 .. n]};
    fi;
    Add(rows, w);
  od;
  ConvertToMatrixRep(rows, q);
  return rows;
end;

# The power <u>^<e> modulo <f>, for e >= 0 and <frob> the matrix of
# RECOG.PolFrobeniusMatrix: the product of the (u^(e_i))^(q^i) for the
# q-adic digits e_i of e. That is one product with the matrix and one of
# polynomials for each digit, where RECOG.PolPowerMod takes about
# 1.2 log_2(q) products of polynomials.
RECOG.PolPowerModFrobenius := function(F, u, e, f, frob)
  local n, digits, powers, r, i, d;

  n := Length(f) - 1;
  digits := CoefficientsQadic(e, Size(F));
  powers := [];
  r := f{[n + 1]};
  for i in [Length(digits), Length(digits) - 1 .. 1] do
    if i < Length(digits) then
      PadCoeffs(r, n);
      r := ShallowCopy(r * frob);
      ShrinkRowVector(r);
    fi;
    d := digits[i];
    if d > 0 then
      if not IsBound(powers[d]) then
        powers[d] := RECOG.PolPowerMod(u, d, f);
      fi;
      r := RECOG.PolProductMod(r, powers[d], f);
    fi;
  od;
  return r;
end;

# The monic irreducible factors of the monic squarefree polynomial <f>
# over <F>, of odd characteristic, by Berlekamp's algorithm. The
# polynomials v with v^q = v modulo f form an F-algebra B, isomorphic to
# F^r for the r irreducible factors of f: the kernel of Q - 1 for the matrix
# Q of the Frobenius map of F[x]/(f). A v in B is a constant c_i modulo the
# i-th factor, and gcd(f, (v + s)^((q-1)/2) - 1) collects the factors with
# c_i + s a nonzero square. A divisor g of f is irreducible if and only if
# all of B is constant modulo g.
# No random numbers are drawn. The cost is that of echelonising a matrix of
# n = deg f rows, where `Factors` takes up to n/2 powers x^(q^i) modulo f
# and as many gcds, and then splits the factors of equal degree.
RECOG.PolFactorsSquarefree := function(F, f)
  local q, n, one, i, M, rank, pivots, cols, basis, j, v, omega, split;

  q := Size(F);
  n := Length(f) - 1;
  if n <= 1 then
    return [f];
  fi;
  one := One(F);

  # B = { v : v (Q - 1) = 0 }, from the reduced echelon form of the
  # transposed matrix: one basis vector for each column without pivot. The
  # first column is zero, which gives the constants; the other basis
  # vectors have constant term 0
  M := MutableCopyMat(TransposedMat(RECOG.PolFrobeniusMatrix(F, f)));
  for i in [1 .. n] do
    M[i, i] := M[i, i] - one;
  od;
  TriangulizeMat(M);
  rank := n;
  while rank > 0 and IsZero(M[rank]) do
    rank := rank - 1;
  od;
  if rank = n - 1 then
    return [f];
  fi;
  pivots := List([1 .. rank], i -> PositionNonZero(M[i]));
  cols := TransposedMat(M);
  basis := [];
  for j in Difference([2 .. n], pivots) do
    v := ZeroMutable(cols[1]);
    v{pivots} := -cols[j]{[1 .. rank]};
    v[j] := one;
    ShrinkRowVector(v);
    Add(basis, v);
  od;

  # the irreducible factors of the divisor g of f
  omega := PrimitiveRoot(F);
  split := function(g)
    local v, i, w, t, parts, rest;

    v := First(List(basis, b -> RECOG.PolMod(b, g)), b -> Length(b) > 1);
    if v = fail then
      return [g];
    fi;
    # the shift by -c_1 splits, so this ends
    i := -1;
    repeat
      w := ShallowCopy(v);
      if i >= 0 then
        w[1] := w[1] + omega^i;
      fi;
      i := i + 1;
      t := RECOG.PolPowerMod(w, (q - 1) / 2, g);
      w := ShallowCopy(t);
      w[1] := w[1] - one;
      ShrinkRowVector(w);
      parts := [GcdCoeffs(g, w)];
      rest := RECOG.PolQuotient(g, parts[1]);
      t[1] := t[1] + one;
      ShrinkRowVector(t);
      Add(parts, GcdCoeffs(rest, t));
      Add(parts, RECOG.PolQuotient(rest, parts[2]));
      parts := Filtered(parts, h -> Length(h) > 1);
    until Length(parts) > 1;
    return Concatenation(List(parts, split));
  end;

  return split(f);
end;
