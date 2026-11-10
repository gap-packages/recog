#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This files's authors include Max Horn, Daniel Rademacher.
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
# ([EHNPR], table of terminal and initial degrees):
#   terminal : degree at which GoingDown stops
#   minBody  : smallest admissible stingray body dimension
#   parity   : parity of all body dimensions, or fail if there is none
#   isNamed  : whether a group of the active degree is the full classical
#              group; this is the naming test of GoingDownStep
RECOG.GoingDownParameters := function(type, q)
  if type = "SL" then
    return rec( terminal := 4, minBody := 2, parity := fail,
                isNamed := H -> RecogniseClassical(H,
                                    rec(case := "linear")).isSLContained = true );
  fi;
  ErrorNoReturn("RECOG.GoingDownParameters: unsupported type ", type);
end;

# The admissible stingray body dimensions in degree <n>:
# minBody <= m <= min(2*ceil(log2(n)), ceil(n/2)-1), of the prescribed
# parity ([EHNPR], degree window). Two such bodies span a space of degree
# at least the terminal degree and less than <n>.
RECOG.StingrayBodyDimensions := function(n, params)
  local D;
  # Log2Int(2*n-1) = ceil(log2(n))
  D := [params.minBody .. Minimum(2 * Log2Int(2 * n - 1), QuoInt(n + 1, 2) - 1)];
  if params.parity <> fail then
    D := Filtered(D, m -> m mod 2 = params.parity);
  fi;
  return D;
end;

# FindStingrayElement of [EHNPR]: search at most <N> random elements of
# <G> for one whose characteristic polynomial has an irreducible factor P
# of multiplicity 1 with deg(P) in <D>, not dividing the degree of any other
# factor. Its power s = h^B, with B killing the other primary components,
# is a deg(P)-stingray element if and only if x^B generates
# GF(q)[x]/<P> over GF(q).
# Returns rec(element := s, dim := deg(P), remaining := random selections
# left), or fail.
RECOG.FindStingrayElement := function(G, D, N)
  local F, q, p, x, h, factors, degrees, i, m, others, c, beta, B, P, gamma;

  F := DefaultFieldOfMatrixGroup(G);
  q := Size(F);
  p := Characteristic(F);
  x := Indeterminate(F);

  while N > 0 do
    h := PseudoRandom(G);
    N := N - 1;
    factors := Collected(Factors(CharacteristicPolynomial(F, F, StripMemory(h))));
    degrees := List(factors, f -> Degree(f[1]));

    for i in [1..Length(factors)] do
      m := degrees[i];
      if factors[i][2] <> 1 or not m in D or
         ForAny([1..Length(factors)], j -> j <> i and degrees[j] mod m = 0) then
        continue;
      fi;

      # B = p^beta * lcm(q^deg(P_j)-1 : j <> i), with p^beta >= every other
      # multiplicity
      others := factors{Difference([1..Length(factors)], [i])};
      c := Maximum(Concatenation([1], List(others, f -> f[2])));
      beta := 0;
      while p^beta < c do
        beta := beta + 1;
      od;
      B := p^beta * Lcm(Concatenation([1], List(others, f -> q^Degree(f[1]) - 1)));

      # x^B generates GF(q^m) if it lies in no maximal subfield GF(q^(m/r))
      P := factors[i][1];
      gamma := PowerMod(x, B, P);
      if ForAll(Set(Factors(m)), r -> PowerMod(gamma, q^(m/r), P) <> gamma) then
        return rec( element := h^B, dim := m, remaining := N );
      fi;
    od;
    Info(InfoRecog_ClassicalNatural, 3,
         "    GoingDown: random element is no pre-stingray candidate");
  od;

  return fail;
end;

# GoingDownStep of [EHNPR]: find stingray elements s1, s2 of <G> whose
# bodies W_i = im(s_i-1) and tails E_i = ker(s_i-1) satisfy
# W1 \cap W2 = 0 and V = (W1+W2) + (E1 \cap E2) (a stingray duo), such
# that the restrictions of s1, s2 to W1+W2 generate the classical group
# there. Uses at most <N> random selections.
# Returns rec(gens := the two restrictions, slp := SLP of [s1,s2] in the
# generators of <G>, basis := a basis of W1+W2 followed by one of
# E1 \cap E2, as a matrix), or fail.
RECOG.GoingDownStep := function(G, params, N)
  local n, F, D, r1, r2, s1, s2, W, E, sum, nn, tail, C, gens;

  n := DimensionOfMatrixGroup(G);
  F := DefaultFieldOfMatrixGroup(G);
  D := RECOG.StingrayBodyDimensions(n, params);

  while N > 0 do
    r1 := RECOG.FindStingrayElement(G, D, N);
    if r1 = fail then
      return fail;
    fi;
    r2 := RECOG.FindStingrayElement(G, D, r1.remaining);
    if r2 = fail then
      return fail;
    fi;
    N := r2.remaining;

    s1 := StripMemory(r1.element);
    s2 := StripMemory(r2.element);
    W := List([s1, s2], s -> SemiEchelonMat(s - One(s)).vectors);
    E := List([s1, s2], RECOG.FixspaceMat);
    sum := SumIntersectionMat(W[1], W[2])[1];
    nn := r1.dim + r2.dim;
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
    return rec( gens := gens,
                slp := SLPOfElms([r1.element, r2.element]),
                basis := C );
  od;

  return fail;
end;

# GoingDown of [EHNPR]: apply GoingDownStep to <G>, a classical group of
# type <type> in its natural representation with generators with memory,
# and then to the group returned, until the terminal degree is reached;
# restart from <G> if a step uses <N> random selections without success.
# Returns rec(gens := generators of the terminal group, as matrices of
# the terminal degree, slp := SLP for them in the generators of <G>,
# bas := a matrix whose first rows span the space on which the terminal
# group acts, and whose other rows span its fixed space) such that
# bas * x * bas^-1 = DiagonalJoin(y, 1) for the elements x of the
# terminal group, y the corresponding matrix of the terminal degree.
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
