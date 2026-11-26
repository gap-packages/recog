#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This file's authors include Max Horn, Daniel Rademacher.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
##
##  GoingDown for classical groups in their natural representation, as in
##  Eisenbrand, Horn, Niemeyer, Praeger, Rademacher, "Constructive
##  recognition of finite classical groups using stingray elements" (in
##  preparation), cited as [EHNPR] below.
##
#############################################################################

# Random selections a GoingDown step may make before GoingDown restarts
RECOG.GoingDownRandomBound := 100;

# The parameters of GoingDown for the classical type <type> over GF(<q>)
# ([EHNPR], Section 'Outline of the algorithm', table of terminal and
# initial degrees):
#   terminal : degree at which GoingDown stops
#   minBody  : smallest admissible stingray body dimension
#   parity   : parity of all body dimensions, or fail if there is none
#   isNamed  : whether a group of the active degree is the full classical
#              group, by RecogniseClassical [NP98]; this is the naming
#              test of GoingDownStep
# All groups of the chain below an orthogonal group are orthogonal, of
# either sign ([EHNPR], 'GoingDown algorithm', remark on the types).
RECOG.GoingDownParameters := function(type, q)
  local q0, m;

  if type = "SL" then
    return rec( terminal := 4, minBody := 2, parity := fail,
                isNamed := H -> RecogniseClassical(H,
                                    rec(case := "linear")).isSLContained = true );
  fi;
  if type = "Sp" and IsEvenInt(q) then
    # the groups of the chain below Sp are orthogonal ([EHNPR], remark on
    # the types), with the parameters of the orthogonal types
    return RECOG.GoingDownParameters("O+", q);
  fi;
  if type = "Sp" then
    return rec( terminal := 8, minBody := 4, parity := 0,
                isNamed := H -> RecogniseClassical(H,
                                    rec(case := "symplectic")).isSpContained = true );
  fi;
  if type = "SU" then
    # q = q0^2. Bodies have odd dimension; over GF(4) none has dimension 3,
    # as an element of SU(3,2) is never irreducible on GF(4)^3 ([EHNPR],
    # Section 'GoingDown algorithm')
    q0 := RootInt(q, 2);
    if q0^2 <> q then
      ErrorNoReturn("RECOG.GoingDownParameters: SU needs a square q");
    fi;
    m := 3;
    if q0 = 2 then
      m := 5;
    fi;
    return rec( terminal := 2 * m, minBody := m, parity := 1,
                isNamed := H -> RecogniseClassical(H,
                                    rec(case := "unitary")).isSUContained = true );
  fi;
  if type in RECOG.OrthogonalTypes then
    # Bodies have even dimension and type -, as the stingray element is
    # irreducible on its body; the sum of two has either type. There is no
    # naming test: RecogniseClassical needs the sign, that is, the form,
    # and [EHNPR] ('Implementation and timing') omits the test and
    # restarts GoingDown instead, as RECOG.GoingDown does.
    return rec( terminal := 8, minBody := 4, parity := 0,
                isNamed := ReturnTrue );
  fi;
  ErrorNoReturn("RECOG.GoingDownParameters: unsupported type ", type);
end;

# The admissible stingray body dimensions in degree <n>:
# minBody <= m <= min(2*ceil(log2(n)), ceil(n/2)-1), of the prescribed
# parity ([EHNPR], Section 'GoingDown algorithm', degree window). Two such
# bodies span a space of degree at least the terminal degree and less than
# <n>.
RECOG.StingrayBodyDimensions := function(n, params)
  local D;
  # Log2Int(2*n-1) = ceil(log2(n))
  D := [params.minBody .. Minimum(2 * Log2Int(2 * n - 1), QuoInt(n + 1, 2) - 1)];
  if params.parity <> fail then
    D := Filtered(D, m -> m mod 2 = params.parity);
  fi;
  return D;
end;

# Degrees of the block phase of RECOG.StingrayFactor: one gcd with f
# covers this many degrees. A multiplication modulo f costs about a 30th of
# a gcd with f; blocks of 8, 16 and 32 degrees perform alike.
RECOG.StingrayDegreeBlock := 16;

# The test of Algorithm FindStingrayElement of [EHNPR], Section 'Stingray
# elements', on the characteristic polynomial <chi> of h over the field
# <F>: an irreducible factor P of <chi> of multiplicity 1 with deg(P) = m in
# <D>, where m divides the degree of no other factor, and x^B generates
# GF(q)[x]/<P> over GF(q) for B = p^beta * lcm(q^deg(P_j)-1 : P_j <> P),
# with p^beta at least every other multiplicity. Then h^B is an
# m-stingray element.
# Only the degrees and multiplicities of the factors matter, so this is a
# distinct-degree factorisation without the equal-degree split. Up to
# degree max(D) it takes one gcd with x^(q^j)-x per degree j and rejects
# <chi> once no m in <D> is left. Above, a factor of f of degree e lies in
# a block [a..b] iff it divides the product of the x^(q^j)-x for j in
# [a..b], as f has no factor of degree < a; so one gcd per block tests
# RECOG.StingrayDegreeBlock degrees, and only a nontrivial gcd is split by
# degree. Most blocks have none, as a random polynomial has few distinct
# factor degrees.
# Returns fail, or a record with components `P` (monic) and `B`, for the
# smallest m.
RECOG.StingrayFactor := function(chi, F, D)
  local q, p, fam, ind, toPol, x, mmax, status, P, found, register, peel, f,
        fc, minusx, pow, j, a, b, pows, prod, cyc, g, gk, k, m, others, c,
        beta, B, gamma;

  q := Size(F);
  p := Characteristic(F);
  fam := FamilyObj(One(F));
  ind := IndeterminateNumberOfUnivariateRationalFunction(chi);
  toPol := cs -> UnivariatePolynomialByCoefficients(fam, cs, ind);
  x := toPol([Zero(F), One(F)]);

  D := Filtered(Set(D), m -> m < Degree(chi));
  if IsEmpty(D) then
    return fail;
  fi;
  mmax := Maximum(D);

  # status[m]: "open" before degree m is reached; "cand" if there is
  # exactly one factor P[m] of degree m, of multiplicity 1, and none of
  # degree a multiple of m so far; else "dead"
  status := [];
  P := [];
  for m in D do
    status[m] := "open";
  od;

  # [degree, largest multiplicity] for each degree of a factor of chi
  found := [];
  register := function(gk, k, mult)
    local m;
    Add(found, [k, mult]);
    for m in D do
      if m = k and status[m] = "open" and Degree(gk) = k and mult = 1 then
        status[m] := "cand";
        P[m] := gk;
      elif k mod m = 0 then
        status[m] := "dead";
      fi;
    od;
  end;

  # removes the factors of the squarefree gk from f and returns their
  # largest multiplicity
  peel := function(gk)
    local mult, h;
    mult := 0;
    h := gk;
    repeat
      f := Quotient(f, h);
      mult := mult + 1;
      h := GcdOp(f, h);
    until Degree(h) = 0;
    return mult;
  end;

  f := chi / LeadingCoefficient(chi);
  fc := CoefficientsOfUnivariatePolynomial(f);
  if q > MAXSIZE_GF_INTERNAL then
    minusx := Immutable([Zero(F), -One(F)]);
  else
    minusx := ImmutableVector(F, [Zero(F), -One(F)]);
  fi;
  # x^(q^j) mod f
  pow := -minusx;
  j := 0;

  # f has no factor of degree <= j; while it can have two
  while Degree(f) >= 2 * (j + 1) do
    a := j + 1;
    if a <= mmax then
      b := a;
    else
      b := Minimum(a + RECOG.StingrayDegreeBlock - 1, QuoInt(Degree(f), 2));
    fi;

    # pows[k-a+1] = x^(q^k) mod f, and prod = prod (x^(q^k) - x) mod f
    pows := [];
    prod := fail;
    for k in [a..b] do
      pow := PowerModCoeffs(pow, Length(pow), q, fc, Length(fc));
      Add(pows, pow);
      cyc := ShallowCopy(pow);
      AddCoeffs(cyc, minusx);
      if prod = fail then
        prod := cyc;
      else
        prod := ProductCoeffs(prod, cyc);
        ReduceCoeffs(prod, fc);
        ShrinkRowVector(prod);
      fi;
    od;
    j := b;

    g := GcdOp(f, toPol(prod));
    if Degree(g) > 0 then
      for k in [a..b] do
        if Degree(g) < k then
          break;
        fi;
        if a = b then
          gk := g;
        else
          # the factors of g of degree k, as those of smaller degree are gone
          cyc := ShallowCopy(pows[k - a + 1]);
          AddCoeffs(cyc, minusx);
          ReduceCoeffs(cyc, CoefficientsOfUnivariatePolynomial(g));
          ShrinkRowVector(cyc);
          gk := GcdOp(g, toPol(cyc));
        fi;
        if Degree(gk) > 0 then
          # g need not be squarefree
          repeat
            g := Quotient(g, gk);
          until Degree(GcdOp(g, gk)) = 0;
          register(gk, k, peel(gk));
        fi;
      od;
      fc := CoefficientsOfUnivariatePolynomial(f);
      pow := ShallowCopy(pow);
      ReduceCoeffs(pow, fc);
      ShrinkRowVector(pow);
    fi;

    for m in D do
      if a <= m and m <= b and status[m] = "open" then
        status[m] := "dead";
      fi;
    od;
    if ForAll(D, m -> status[m] = "dead") then
      return fail;
    fi;
  od;

  # f is 1 or irreducible of degree > j
  if Degree(f) > 0 then
    register(f, Degree(f), 1);
  fi;

  for m in D do
    if status[m] <> "cand" then
      continue;
    fi;
    others := Filtered(found, r -> r[1] <> m);
    c := Maximum(Concatenation([1], List(others, r -> r[2])));
    # the least beta with p^beta >= c
    beta := LogInt(p * c - 1, p);
    B := p^beta * Lcm(Concatenation([1], List(others, r -> q^r[1] - 1)));

    # x^B generates GF(q^m) if it lies in no maximal subfield GF(q^(m/r));
    # x^(q^m-1) = 1 modulo P, as P is irreducible of degree m and not x
    gamma := PowerMod(x, B mod (q^m - 1), P[m]);
    if ForAll(PrimeDivisors(m), r -> PowerMod(gamma, q^(m/r), P[m]) <> gamma) then
      return rec( P := P[m] / LeadingCoefficient(P[m]), B := B );
    fi;
  od;
  return fail;
end;

# Algorithm FindStingrayElement of [EHNPR], Section 'Stingray elements':
# search at most <N> random elements h of <G> for one that passes
# RECOG.StingrayFactor, with factor P of degree m and exponent B, so that
# s = h^B is an m-stingray element.
# s is computed on the body ker P(h) of h, where h^B = h^(B mod (q^m-1)),
# and is the identity on the tail im P(h) ([EHNPR], remark after the
# algorithm); this avoids powering h in full degree.
# Returns either fail, or else a record with the following components:
#  - `element`: the stingray element s, without memory
#  - `dim`: deg(P), the dimension of its body
#  - `remaining`: the number of random selections left
#  - `body`, `tail`: bases of the body im(s-1) and the tail ker(s-1)
#  - `candidate`, `exponent`: h, with memory, and B, so that s = h^B
RECOG.FindStingrayElement := function(G, D, N)
  local F, q, h, mat, t, P, B, m, T, U, E, A, C, K;

  F := DefaultFieldOfMatrixGroup(G);
  q := Size(F);

  while N > 0 do
    h := PseudoRandom(G);
    N := N - 1;
    mat := StripMemory(h);
    t := RECOG.StingrayFactor(CharacteristicPolynomial(F, F, mat), F, D);
    if t = fail then
      Info(InfoRecog_ClassicalNatural, 3,
           "    GoingDown: random element is no pre-stingray candidate");
      continue;
    fi;
    P := t.P;
    B := t.B;
    m := Degree(P);

    # U = ker P(h) is the body, E = im P(h) the tail, and A is h
    # restricted to U; in the basis C = [U, E], s = diag(A^B, 1), so
    # s - 1 = K * (A^B - 1) * U with K the first m columns of C^-1
    T := SemiEchelonMatTransformation(Value(P, mat));
    U := T.relations;
    E := T.vectors;
    ConvertToMatrixRep(U, F);
    ConvertToMatrixRep(E, F);
    A := List(U * mat, v -> SolutionMat(U, v));
    ConvertToMatrixRep(A, F);
    C := Concatenation(U, E);
    ConvertToMatrixRep(C, F);
    K := (C^-1){[1..Length(C)]}{[1..m]};
    ConvertToMatrixRep(K, F);
    return rec( element := One(mat) + K * ((A^(B mod (q^m - 1)) - One(A)) * U),
                dim := m, remaining := N, body := U, tail := E,
                candidate := h, exponent := B );
  od;

  return fail;
end;

# SLP for the stingray elements of the records <rs> returned by
# RECOG.FindStingrayElement, followed by the elements <elms> with memory,
# in the generators of the group they were found in
RECOG.StingraySLP := function(rs, elms)
  local k, l;
  k := Length(rs);
  l := k + Length(elms);
  return CompositionOfStraightLinePrograms(
             StraightLineProgram(
                 Concatenation(List([1..k], i -> [i, rs[i].exponent]),
                               [Concatenation(List([l+1..l+k], i -> [i, 1]),
                                              List([k+1..l], i -> [i, 1]))]),
                 l),
             SLPOfElms(Concatenation(List(rs, r -> r.candidate), elms)));
end;

# Algorithm GoingDownStep of [EHNPR], Section 'GoingDown algorithm': find
# stingray elements s1, s2 of <G> whose bodies W_i = im(s_i-1) and tails
# E_i = ker(s_i-1) satisfy W1 \cap W2 = 0 and V = (W1+W2) + (E1 \cap E2)
# (a stingray duo), such that the restrictions of s1, s2 to W1+W2
# generate the classical group there. Uses at most <N> random selections.
# Unlike [EHNPR], s2 is a random conjugate s1^g rather than a second
# stingray element, which saves the search for one. It neither restricts
# nor returns a form, as
# RecogniseClassical computes the form itself, and it does not return the
# remaining bound, as GoingDown gives every step <N>.
# Returns either fail, or else a record with the following components:
#  - `gens`: the restrictions of s1, s2 to W1+W2
#  - `slp`: SLP of [s1,s2] in the generators of <G>
#  - `basis`: a basis of W1+W2 followed by one of E1 \cap E2, as a matrix
RECOG.GoingDownStep := function(G, params, N)
  local n, F, D, r, g, gm, s1, s2, W, E, sum, nn, tail, C, gens;

  n := DimensionOfMatrixGroup(G);
  F := DefaultFieldOfMatrixGroup(G);
  D := RECOG.StingrayBodyDimensions(n, params);

  while N > 0 do
    r := RECOG.FindStingrayElement(G, D, N);
    if r = fail or r.remaining = 0 then
      return fail;
    fi;
    g := PseudoRandom(G);
    N := r.remaining - 1;

    # body and tail of s1^g are those of s1 times g
    gm := StripMemory(g);
    s1 := r.element;
    s2 := gm^-1 * s1 * gm;
    W := [r.body, r.body * gm];
    E := [r.tail, r.tail * gm];
    sum := SumIntersectionMat(W[1], W[2])[1];
    nn := 2 * r.dim;
    tail := SumIntersectionMat(E[1], E[2])[2];
    C := Concatenation(sum, tail);
    if Length(sum) <> nn or Length(tail) <> n - nn or RankMat(C) <> n then
      Info(InfoRecog_ClassicalNatural, 3,
           "    GoingDown: stingray elements are no stingray duo");
      continue;
    fi;

    # W1+W2 is s_i-invariant, so its basis times s_i is a combination of it
    gens := List([s1, s2], s -> List(sum * s, v -> SolutionMat(sum, v)));
    Perform(gens, function(g) ConvertToMatrixRep(g, F); end);
    if FieldOfMatrixList(gens) <> F or not params.isNamed(Group(gens)) then
      Info(InfoRecog_ClassicalNatural, 3,
           "    GoingDown: naming test failed in degree ", nn);
      continue;
    fi;

    ConvertToMatrixRep(C, F);
    # [s1, s2] = [h^B, g^-1 * h^B * g] in [h, g]
    return rec( gens := gens,
                slp := CompositionOfStraightLinePrograms(
                           StraightLineProgram([[1, r.exponent], [2, -1, 3, 1, 2, 1],
                                                [[3, 1], [4, 1]]], 2),
                           SLPOfElms([r.candidate, g])),
                basis := C );
  od;

  return fail;
end;

# GoingDown of [EHNPR], Section 'GoingDown algorithm': apply
# GoingDownStep to <G>, a classical group of type <type> in its natural
# representation with generators with memory, and then to the group
# returned, until the terminal degree is reached; restart from <G> if a
# step uses <N> random selections without success. [EHNPR] instead shares
# one bound among all steps and returns fail when it is used up; the
# restart is one of the variants in its Section 'Implementation and
# timing', and spares the callers a fail case.
# Returns a record with the following components:
#  - `gens`: generators of the terminal group, as matrices of the terminal
#    degree
#  - `slp`: SLP for them in the generators of <G>
#  - `bas`: a matrix whose first rows span the space on which the terminal
#    group acts, and whose other rows span its fixed space, such that
#    bas * x * bas^-1 = DiagonalJoin(y, 1) for the elements x of the
#    terminal group, y the corresponding matrix of the terminal degree;
#    bas is L^-1 for the matrix L of [EHNPR]
RECOG.GoingDown := function(G, type, N)
  local d, F, params, H, n, bas, slp, step;

  d := DimensionOfMatrixGroup(G);
  F := DefaultFieldOfMatrixGroup(G);
  params := RECOG.GoingDownParameters(type, Size(F));
  if d < params.terminal then
    ErrorNoReturn("RECOG.GoingDown: degree ", d,
                  " is below the terminal degree ", params.terminal);
  fi;

  repeat
    H := G;
    n := d;
    bas := IdentityMat(d, F);
    slp := SLPOfElms(GeneratorsOfGroup(G));
    while n > params.terminal do
      step := RECOG.GoingDownStep(H, params, N);
      if step = fail then
        Info(InfoRecog_ClassicalNatural, 2,
             "  GoingDown: no step from degree ", n, ", restart");
        break;
      fi;
      Info(InfoRecog_ClassicalNatural, 2, "  GoingDown: degree ", n, " -> ",
           Length(step.gens[1]));
      slp := CompositionOfStraightLinePrograms(step.slp, slp);
      bas := Concatenation(step.basis * bas{[1..n]}, bas{[n+1..d]});
      n := Length(step.gens[1]);
      H := GroupWithMemory(step.gens);
    od;
  until n = params.terminal;

  ConvertToMatrixRep(bas, F);
  return rec( gens := StripMemory(GeneratorsOfGroup(H)), slp := slp, bas := bas );
end;
