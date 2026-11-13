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
##  FinalDescent for orthogonal groups, q odd, from Omega^+-(8,q) to
##  Omega^+(6,q), and constructive recognition of Omega^+(6,q) in its
##  natural representation by the Klein correspondence: SL(4,q) acts on
##  the exterior square L = Lambda^2(GF(q)^4) with kernel <-1> and image
##  Omega^+(6,q), for the quadratic form Q given by w ^ w = 2 Q(w)
##  b_1 ^ b_2 ^ b_3 ^ b_4.
##
##  L has the basis b_ij = b_i ^ b_j, i < j, in the order b_12, b_13, b_14,
##  b_23, b_24, b_34, and Q(sum p_ij b_ij) = p_12 p_34 - p_13 p_24 +
##  p_14 p_23; so (b_12, b_34, b_13, -b_24, b_14, b_23) is a standard basis
##  (e_1, f_1, e_2, f_2, e_3, f_3). For A in GL(4,q), Lambda^2(A) maps b_ij
##  to the sum of the 2x2 minors A{[i,j]}{[k,l]} times b_kl.
##
#############################################################################

# The index pairs of the basis of L, in this order
RECOG.O_KleinPairs := [[1, 2], [1, 3], [1, 4], [2, 3], [2, 4], [3, 4]];

# The coordinates of <x> ^ <y> in L, for x, y in GF(q)^4
RECOG.O_Wedge := {x, y} -> List(RECOG.O_KleinPairs,
    kl -> x[kl[1]] * y[kl[2]] - x[kl[2]] * y[kl[1]]);

# Lambda^2(<A>) for a 4x4 matrix <A> over <f>, relative to the basis b_ij
RECOG.O_Wedge2 := function(A, f)
  local res;
  res := List(RECOG.O_KleinPairs, ij -> RECOG.O_Wedge(A[ij[1]], A[ij[2]]));
  ConvertToMatrixRep(res, f);
  return res;
end;

# A matrix A in SL(4,q), q = Size(<f>), with Lambda^2(A) = <M>, or fail if
# there is none; A is unique up to sign. The row a_i of A spans the
# vectors v with v ^ (a_i ^ a_j) = 0 for all j <> i, and the rows
# M[b_ij] = a_i ^ a_j fix the scalars of the a_i up to a common sign.
RECOG.O_KleinPreimage := function(M, f)
  local P, wedgeMat, a, i, X, N, ratio, c, A;

  P := ij -> Position(RECOG.O_KleinPairs, ij);

  # the 4x4 matrix of v -> v ^ w, w in L, relative to the basis
  # b_123, b_124, b_134, b_234 of Lambda^3(GF(q)^4)
  wedgeMat := w -> List(IdentityMat(4, f), v -> [
      v[1] * w[P([2, 3])] - v[2] * w[P([1, 3])] + v[3] * w[P([1, 2])],
      v[1] * w[P([2, 4])] - v[2] * w[P([1, 4])] + v[4] * w[P([1, 2])],
      v[1] * w[P([3, 4])] - v[3] * w[P([1, 4])] + v[4] * w[P([1, 3])],
      v[2] * w[P([3, 4])] - v[3] * w[P([2, 4])] + v[4] * w[P([2, 3])] ]);

  a := [];
  for i in [1 .. 4] do
    X := List(Difference([1 .. 4], [i]), j -> wedgeMat(M[P(Set([i, j]))]));
    N := NullspaceMat(List([1 .. 4], r -> Concatenation(List(X, x -> x[r]))));
    if Length(N) <> 1 then
      return fail;
    fi;
    a[i] := N[1];
  od;

  # c_i c_j = M[b_ij] / (a_i ^ a_j)
  ratio := function(i, j)
    local w, k;
    w := RECOG.O_Wedge(a[i], a[j]);
    k := PositionNonZero(w);
    return M[P([i, j]), k] / w[k];
  end;
  c := [RootFFE(f, ratio(1, 2) * ratio(1, 3) / ratio(2, 3), 2)];
  if c[1] = fail then
    return fail;
  fi;
  for i in [2 .. 4] do
    c[i] := ratio(1, i) / c[1];
  od;
  A := List([1 .. 4], i -> c[i] * a[i]);
  ConvertToMatrixRep(A, f);
  if RECOG.O_Wedge2(A, f) <> M then
    return fail;
  fi;
  return A;
end;

# The rows of the basis b_12, b_13, b_14, b_23, b_24, b_34 of L, given the
# rows <B> of the standard basis (e_1, f_1, e_2, f_2, e_3, f_3) which they
# correspond to
RECOG.O_KleinBasis := B -> [B[1], B[3], B[5], B[6], -B[4], B[2]];

# Matrices A in SL(4,q), q = Size(<f>), whose images Lambda^2(A) are the
# standard generators s, t, delta, s', t', delta', v of Omega^+(6,q),
# relative to the basis b_ij of L (see the top of this file): with
# gamma = Z(q), the first three lie in SL(2,q) on <b_1, b_4>, the next
# three in SL(2,q) on <b_2, b_3>, and v is the cycle b_2 -> b_3 -> b_4.
RECOG.O_KleinStandardPreimages := function(f)
  local gamma, one, res;

  gamma := Z(Size(f));
  one := One(f);
  res := [ RECOG.EmbedBlock(4, f, [1, 4], [[0, -1], [1, 0]]),
           RECOG.EmbedBlock(4, f, [1, 4], [[1, -1], [0, 1]]),
           DiagonalMat([gamma, one, one, gamma^-1]),
           RECOG.EmbedBlock(4, f, [2, 3], [[0, 1], [-1, 0]]),
           RECOG.EmbedBlock(4, f, [2, 3], [[1, 1], [0, 1]]),
           DiagonalMat([one, gamma, gamma^-1, one]),
           RECOG.SignedCycle(4, f, [2, 3, 4], 1) ];
  Perform(res, function(A) ConvertToMatrixRep(A, f); end);
  return res;
end;

# The preimages in SL(4,q) of the 6x6 matrices <gens> over <f> which
# preserve the symmetric form <form> of type +, relative to the basis K of
# L of the standard basis <B> of <form>, or fail if one of them has none
RECOG.O_KleinLift := function(gens, B, f)
  local K, Ki, res;

  K := RECOG.O_KleinBasis(B);
  ConvertToMatrixRep(K, f);
  Ki := K^-1;
  res := List(gens, g -> RECOG.O_KleinPreimage(K * g * Ki, f));
  if fail in res then
    return fail;
  fi;
  return res;
end;

# Whether the 6x6 matrices <gens> over <f>, which preserve the symmetric
# form <form> of type + and act as elements of Omega on GF(q)^6, generate
# Omega^+(6,q): whether their preimages in SL(4,q) generate it, by
# RecogniseClassical. Returns the preimages if so, and fail otherwise.
RECOG.O_IsOmega6 := function(gens, form, f)
  local B, A;

  B := RECOG.FormStandardBasis(form, IdentityMat(6, f));
  A := RECOG.O_KleinLift(gens, B, f);
  if A = fail or FieldOfMatrixList(A) <> f or
     RecogniseClassical(Group(A), rec(case := "linear")).isSLContained <> true
     then
    return fail;
  fi;
  return A;
end;

# Constructive recognition of Omega^+(6,q), q odd, in its natural
# representation, by the Klein correspondence: <gens> are 6x6 matrices over
# <f> which generate Omega^+(6,q) and preserve the symmetric form <form>,
# a form record. For a standard basis B of <form> and the basis K of L it
# corresponds to, the preimages in SL(4,q) of the matrices of <gens>
# relative to K generate SL(4,q), which is recognised as in
# RECOG.FindStdGens_SL: RECOG.SLn_FinalDescent and the GoingUp from
# SL(2,q). The standard generators of Omega^+(6,q) relative to B are then
# Lambda^2 of the elements of RECOG.O_KleinStandardPreimages, which
# RECOG.SL_ExpressByElementary writes in the standard generators of
# SL(4,q); as Lambda^2 is a homomorphism, the same SLPs evaluated in
# <gens> give them.
# The thesis [DR] (see ../SU/BaseCase.gi), Section 8.1, names Brooksbank
# and Kantor for Omega^+(6,q) instead.
# Returns a record with the following components:
#  - `slp`: SLP in <gens> for the standard generators of Omega^+(6,q),
#    relative to bas
#  - `bas`: a standard basis of <form>, as a 6x6 matrix
RECOG.O_FindStdGensOmega6 := function(gens, form, f)
  local B, A, h, init, slp, up, Y, R, E, words;

  B := RECOG.FormStandardBasis(form, IdentityMat(6, f));
  ConvertToMatrixRep(B, f);
  A := RECOG.O_KleinLift(gens, B, f);
  if A = fail then
    ErrorNoReturn("RECOG.O_FindStdGensOmega6: <gens> do not lie in ",
                  "Omega^+(6,q)");
  fi;

  h := GroupWithMemory(A);
  init := RECOG.SLn_FinalDescent(A, f);
  slp := CompositionOfStraightLinePrograms(RECOG.SL2_FromMakeSLStdGens(f),
                                           init.slp);
  up := RECOG.GoingUp(h, "SL", rec( slp := slp, bas := init.bas, n := 2 ));

  Y := GeneratorsWithMemory(ListWithIdenticalEntries(5, ()));
  R := RECOG.SL_RootElements(Y, 4, f);
  E := {i, j, lambda} -> RECOG.SL_ElementaryMatrix(R, i, j, lambda);
  words := List(RECOG.O_KleinStandardPreimages(f),
                M -> RECOG.SL_ExpressByElementary(up.bas * M * up.bas^-1, E,
                                                  R.one));
  return rec( slp := CompositionOfStraightLinePrograms(SLPOfElms(words),
                                                       up.slp),
              bas := B );
end;

# FinalDescent of [EHNPR] (see ../GoingDown.gi; 'Terminal groups and
# initial groups', 'The final descent') for orthogonal groups, q odd:
# <gens> are 8x8 matrices over <f> generating Omega^+-(8,q), which preserve
# the symmetric form <form>, a form record. A stingray element s with a
# body W of dimension 4 and an involution j whose (-1)-eigenspace D has
# dimension 2 are taken as a stingray duo, as in RECOG.GoingDownStep: if W
# meets D trivially and V is the sum of W + D and the common fixed space,
# then <s, j> acts on W + D and fixes its complement. If W + D has type +
# and the preimages of s and j in SL(4,q) generate SL(4,q), then <s, j>
# induces Omega^+(6,q) on W + D.
# The routes [EHNPR] sketches do not cover all these groups. The
# centraliser of an involution with eigenspaces E2 and E6 of dimensions 2
# and 6 ([DR], Section 8.1) needs E6 of type +, but the spinor norm of an
# involution is the discriminant of its (-1)-eigenspace, so it is a square
# in Omega; in Omega^+(8,q) with q = 3 mod 4, where -1 is a non-square,
# E2 and E6 have type - then. Stingray duos with bodies of dimensions 4 and
# 2 ([EHNPR], remark on the smallest stingray bodies) need a 2-stingray
# element, which Omega^+(8,q) has rarely for large q and Omega^+-(8,3) not
# at all. Here j takes its place: D may have type -, so such involutions
# lie in Omega for every q. No success probability is known; over 10 seeds
# for each Omega^+-(8,q), q <= 243 odd, every run succeeded, and 240 of
# the 244 duos of type + generated Omega^+(6,q).
# Makes at most <N> random selections of a stingray element or an
# involution, and returns fail if they are used up. Otherwise it returns a
# record with the following components:
#  - `slp`: SLP in <gens> for the standard generators of an Omega^+(6,q)
#  - `bas`: an 8x8 matrix whose first six rows are a standard basis of
#    <form> restricted to the space on which this Omega^+(6,q) acts, and
#    whose last two span its fixed space; relative to bas the standard
#    generators are those of RECOG.ClassicalStandardGenerators("O+", 6, <f>),
#    extended by the identity on the last two rows
RECOG.O_FinalDescent := function(gens, f, form, N)
  local h, ord, pr, r, j, s, jm, W, sum, tail, H6, form6, base;

  if NrRows(gens[1]) <> 8 then
    ErrorNoReturn("RECOG.O_FinalDescent: <gens> must be 8x8 matrices");
  fi;

  h := GroupWithMemory(gens);
  ord := g -> Order(StripMemory(g));
  pr := ProductReplacer(GeneratorsOfGroup(h));
  while N > 0 do
    r := RECOG.FindStingrayElement(h, [4], N);
    if r = fail then
      return fail;
    fi;
    N := r.remaining;
    j := fail;
    while j = fail and N > 0 do
      N := N - 1;
      j := RECOG.InvolutionSearcher(pr, ord, 100);
      if j <> fail and Length(RECOG.FixspaceMat(-StripMemory(j))) <> 2 then
        j := fail;
      fi;
    od;
    if j = fail then
      return fail;
    fi;

    s := StripMemory(r.element);
    jm := StripMemory(j);
    W := SemiEchelonMatTransformation(s - One(s));
    sum := SumIntersectionMat(W.vectors, RECOG.FixspaceMat(-jm))[1];
    tail := SumIntersectionMat(W.relations, RECOG.FixspaceMat(jm))[2];
    if Length(sum) <> 6 or Length(tail) <> 2
       or RankMat(Concatenation(sum, tail)) <> 8 then
      Info(InfoRecog_ClassicalNatural, 3,
           "    FinalDescent: stingray element and involution are no duo");
      continue;
    fi;
    if RECOG.FormOrthogonalType(form, sum) <> "O+" then
      Info(InfoRecog_ClassicalNatural, 3,
           "    FinalDescent: the sum of the bodies has type -");
      continue;
    fi;
    H6 := List([s, jm], g -> List(sum * g, v -> SolutionMat(sum, v)));
    Perform(H6, function(g) ConvertToMatrixRep(g, f); end);
    form6 := rec( gram := RECOG.FormGram(form, sum), frob := 1, field := f );
    if RECOG.O_IsOmega6(H6, form6, f) = fail then
      Info(InfoRecog_ClassicalNatural, 3,
           "    FinalDescent: the duo does not generate Omega^+(6,q)");
      continue;
    fi;

    base := RECOG.O_FindStdGensOmega6(H6, form6, f);
    return rec( slp := CompositionOfStraightLinePrograms(base.slp,
                           SLPOfElms([r.element, j])),
                bas := Concatenation(base.bas * sum, tail) );
  od;
  return fail;
end;
