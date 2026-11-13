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
##  [EHNPR] (see GoingDown.gi), Section 'GoingUp algorithm', for SL.
##
##  A GoingUp step ([EHNPR], 'The GoingUpStep algorithm', whose steps are
##  numbered as here) starts from a stingray embedding: a basis B of
##  V = GF(q)^d, whose first n vectors span U, and words for the standard
##  generators Y of CL(U) relative to these vectors, extended by the
##  identity on T = <v_(n+1), ..., v_d>. With the overlap k = 1 for SL, it
##  constructs the same for degree n' = min(2n - k, d), keeping the first n
##  vectors of B:
##
##     U = A + P, P = <v_(n-k+1), ..., v_n> the pivot space
##     1. t in <Y> whose fixed space on U has dimension k (the seed)
##     2. g = t^a for random a, until W = U + Ug has dimension n', T meets
##        Fix(g) in a complement of W, and U meets Fix(g) in a suitable
##        k-space P'
##     3. g~ = g^b with b in <Y> mapping P' onto P, so that g~ fixes P
##     4. v_(n+1), ..., v_d := a basis of N, the projection of A g~ to T,
##        and fixed vectors of g~ in T; so W = U + N
##     5. the standard generators of CL(W) as words in Y and g~
##
#############################################################################

# Random selections a GoingUp step may make before it returns fail
RECOG.GoingUpRandomBound := 100;

# The functions of the GoingUp step for the classical type <type>, and its
# overlap k (see the top of this file). rootElements(n, f) returns the
# record of root elements of CL(n,q), whose component Y holds the words
# standing for the standard generators. The other functions are documented
# where they are defined, in SL/GoingUp.gi.
RECOG.GoingUpParameters := function(type)
  if type = "SL" then
    return rec( overlap := 1,
                rootElements := {n, f} -> RECOG.SL_RootElements(
                    GeneratorsWithMemory(ListWithIdenticalEntries(5, ())),
                    n, f),
                doublingElement := RECOG.SL_GoingUpDoublingElement,
                adaptBasis := RECOG.SL_GoingUpAdaptBasis,
                newGenerators := RECOG.SL_GoingUpNewGenerators );
  fi;
  ErrorNoReturn("RECOG.GoingUpParameters: unsupported type ", type);
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
# algorithm') for the type <type>, "SL": <G> is SL(d,q) with generators
# with memory, and <init> describes an embedded CL(n,q) as follows:
#  - `slp`: SLP in the generators of <G> for the standard generators of
#    CL(n,q), as in RECOG.ClassicalStandardGenerators, relative to bas
#  - `bas`: a d x d matrix whose last d-n rows are fixed by that CL(n,q)
#  - `n`: the degree n, at least 2
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
