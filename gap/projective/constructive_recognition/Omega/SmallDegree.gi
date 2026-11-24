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
##  Constructive recognition of the orthogonal groups of degree less than
##  8 in their natural representation, by the exceptional isomorphisms
##  with classical groups of smaller degree (Kleidman and Liebeck, The
##  subgroup structure of the finite classical groups, 1990, Proposition
##  2.9.1): the generators are lifted to the covering group, which is
##  recognised by its own code, and the standard generators of Omega are
##  written in those of the covering group.
##
##  Omega(5,q) = Sp(4,q)/<-1> and Omega^-(6,q) = SU(4,q)/<-1> come from the
##  Klein correspondence Omega^+(6,q) = SL(4,q)/<-1> of BaseCase.gi. With w'
##  orthogonal to the space V of Omega(5,q) and Q(w') = -Q(w_1), V + <w'>
##  has type +, and Omega(5,q) is the stabiliser of w' in Omega^+(6,q); its
##  preimage fixes the alternating form which is w' as an element of the
##  exterior square. The space of Omega^-(6,q) has type + over GF(q^2), and
##  the preimage of Omega^-(6,q) in SL(4,q^2) is a conjugate of SU(4,q).
##
##  Omega^-(4,q) = SL(2,q^2)/<-1> has one hyperbolic pair, for which
##  RECOG.Form_Rewrite has no root elements; it is rewritten by
##  RECOG.Omega_RankOneRewrite.
##
#############################################################################

# The covering group of Omega(<d>,q) of type <type>, q = Size(<f>): "O" with
# d = 5 and q odd, or "O-" with d = 6. Returns a record with the
# following components:
#  - `type`, `field`: the covering group is a conjugate of the group of
#    that type of degree 4 over that field
#  - `lift`: a function which maps a matrix of Omega(d,q), relative to a
#    standard basis, to one of its two preimages, or to fail if it has none
# The standard basis is extended by w' for d = 5, and e_3, f_3 is a
# hyperbolic pair of <w_1, w'> resp. of <w_1, w_2> over GF(q^2): for q
# odd, w_1 + w' and w' - w_1 resp. alpha w_1 + w_2 and (alpha w_1 - w_2) /
# (-4 gamma) with alpha^2 = gamma = Z(q); for q even h w_1 + w_2 and
# (h^q w_1 + w_2) / eta^2 with h = Z(q^2) and eta = h + h^q.
RECOG.Omega_SmallDegreeCover := function(type, d, f)
  local q, F, C, res, alpha, h, K, Ki;

  q := Size(f);
  if type = "O" and d = 5 and IsOddInt(q) then
    F := f;
    C := IdentityMat(6, F);
    C[5]{[5, 6]} := [One(F), One(F)];
    C[6]{[5, 6]} := [-One(F), One(F)];
    res := rec( type := "Sp", field := F );
  elif type = "O-" and d = 6 then
    F := GF(q^2);
    C := IdentityMat(6, F);
    if IsEvenInt(q) then
      h := Z(q^2);
      C[5]{[5, 6]} := [h, One(F)];
      C[6]{[5, 6]} := [h^q, One(F)] / RECOG.OrthogonalEta(q)^2;
    else
      alpha := Z(q^2)^((q + 1) / 2);
      C[5]{[5, 6]} := [alpha, One(F)];
      C[6]{[5, 6]} := [alpha, -One(F)] / (-4 * Z(q));
    fi;
    res := rec( type := "SU", field := F );
  else
    ErrorNoReturn("RECOG.Omega_SmallDegreeCover: unsupported group");
  fi;

  K := RECOG.Omega_KleinBasis(C);
  ConvertToMatrixRep(K, F);
  Ki := K^-1;
  res.lift := function(M)
    if d = 5 then
      M := DirectSumMat(M, [[One(F)]]);
    fi;
    return RECOG.Omega_KleinPreimage(K * M * Ki, F);
  end;
  return res;
end;

# RECOG.FindStdGens_Omega for degree 5 and 6: <G> is a group with memory
# which is Omega(d,q) of type <type>, with q odd for d = 5. Omega^+(6,q)
# is left to RECOG.FindStdGensOmega6. Otherwise the generators, relative
# to a standard basis B, are lifted to the covering group, a conjugate of
# Sp(4,q) or SU(4,q), which RECOG.FindStdGens_Sp or RECOG.FindStdGens_SU
# recognise; the lifts of the standard generators of Omega(d,q) are
# rewritten in the standard generators of the covering group, and these
# words give them in G, relative to B.
RECOG.FindStdGens_SmallOmega := function(G, type)
  local f, d, gens, form, B, Bi, base, cover, A, std, W, words;

  f := FieldOfMatrixGroup(G);
  d := DimensionOfMatrixGroup(G);
  gens := StripMemory(GeneratorsOfGroup(G));
  form := RECOG.ClassicalInvariantForm(type, gens, f);
  if type = "O+" and d = 6 then
    base := RECOG.FindStdGensOmega6(gens, form, f);
    return rec( type := type, slpstd := base.slp, bas := base.bas,
                basi := base.bas^-1 );
  fi;

  B := RECOG.FormStandardBasis(form, IdentityMat(d, f));
  ConvertToMatrixRep(B, f);
  Bi := B^-1;
  cover := RECOG.Omega_SmallDegreeCover(type, d, f);
  A := List(gens, g -> cover.lift(B * g * Bi));
  if fail in A then
    ErrorNoReturn("RECOG.FindStdGens_SmallOmega: the generators do not ",
                  "lie in Omega");
  fi;
  Info(InfoRecog_ClassicalNatural, 1, "Omega_n: ", type, "(", d, ",",
       Size(f), ") by its covering group ", cover.type, "(4)");
  if cover.type = "Sp" then
    std := RECOG.FindStdGens_Sp(GroupWithMemory(A));
  else
    std := RECOG.FindStdGens_SU(GroupWithMemory(A));
  fi;

  W := RECOG.Form_RewriteSetup(cover.type, 4, cover.field);
  words := List(RECOG.ClassicalStandardGenerators(type, d, f).all,
                x -> RECOG.Form_Rewrite(W, std.bas * cover.lift(x)
                                           * std.basi));
  return rec( type := type,
              slpstd := CompositionOfStraightLinePrograms(
                            IntegratedStraightLineProgram(words), std.slpstd),
              bas := B, basi := Bi );
end;

# The covering group SL(2,q^2) of Omega^-(4,q), q = Size(<f>); <type> is
# "O-" and <d> is 4. Returns a record with the components `field` and
# `lift` of RECOG.Omega_SmallDegreeCover.
# A in SL(2,q^2) acts on the hermitian 2x2 matrices X over GF(q^2), a
# space of dimension 4 over GF(q), by X -> conj(A)^T X A, and preserves
# Q = det, which has the standard basis E_11, E_22, E_12 + E_21,
# alpha E_12 - alpha E_21 for q odd, alpha^2 = Z(q), resp. E_11, E_22,
# E_12 + E_21, h E_12 + h^q E_21 for q even, h = Z(q^2). Relative to the
# basis E_11, E_12, E_21, E_22 this map is the Kronecker product of conj(A)
# with A, whose 2x2 blocks are multiples of A.
RECOG.Omega_RankOneCover := function(type, d, f)
  local q, F, one, P, star, Pi, alpha;

  q := Size(f);
  if type = "O-" and d = 4 then
    F := GF(q^2);
    one := One(F);
    if IsEvenInt(q) then
      alpha := Z(q^2);
    else
      alpha := Z(q^2)^((q + 1) / 2);
    fi;
    P := [[1, 0, 0, 0], [0, 0, 0, 1], [0, 1, 1, 0],
          [0, alpha, alpha^q, 0]] * one;
    star := A -> List(A, r -> List(r, x -> x^q));
  else
    ErrorNoReturn("RECOG.Omega_RankOneCover: unsupported group");
  fi;
  ConvertToMatrixRep(P, F);
  Pi := P^-1;

  return rec( field := F, lift := function(M)
    local K, pos, A, lambda;

    K := Pi * M * P;
    # a nonzero block
    pos := First(Cartesian([1, 2], [1, 2]),
                 ik -> not IsZero(K{2 * ik[1] + [-1, 0]}{2 * ik[2] + [-1, 0]}));
    A := K{2 * pos[1] + [-1, 0]}{2 * pos[2] + [-1, 0]};
    lambda := RootFFE(F, DeterminantMat(A)^-1, 2);
    if lambda = fail then
      return fail;
    fi;
    A := lambda * A;
    ConvertToMatrixRep(A, F);
    if KroneckerProduct(star(A), A) <> K then
      return fail;
    fi;
    return A;
  end );
end;

# RECOG.FindStdGens_Omega for Omega^-(4,q): as RECOG.FindStdGens_SmallOmega,
# with the covering group SL(2,q^2) of RECOG.Omega_RankOneCover, recognised
# by RECOG.RecogniseSL2Natural.
RECOG.FindStdGens_RankOneOmega := function(G, type)
  local f, d, gens, form, B, Bi, cover, A, sl, fake, Y, std, words, i;

  f := FieldOfMatrixGroup(G);
  d := DimensionOfMatrixGroup(G);
  gens := StripMemory(GeneratorsOfGroup(G));
  form := RECOG.ClassicalInvariantForm(type, gens, f);
  B := RECOG.FormStandardBasis(form, IdentityMat(d, f));
  ConvertToMatrixRep(B, f);
  Bi := B^-1;
  cover := RECOG.Omega_RankOneCover(type, d, f);
  A := List(gens, g -> cover.lift(B * g * Bi));
  if fail in A then
    ErrorNoReturn("RECOG.FindStdGens_RankOneOmega: the generators do not ",
                  "lie in Omega");
  fi;
  Info(InfoRecog_ClassicalNatural, 1, "Omega_n: ", type, "(", d, ",",
       Size(f), ") by its covering group SL(2,", Size(cover.field), ")");
  sl := RECOG.RecogniseSL2Natural(GroupWithMemory(A), cover.field);

  # s, t, delta; u and v are the identity
  fake := RECOG.InitSLfake(cover.field, 2);
  Y := GeneratorsWithMemory(List(sl.all, x -> ()));
  std := RECOG.ClassicalStandardGenerators(type, d, f).all;
  words := ListWithIdenticalEntries(Length(std), One(Y[1]));
  for i in [1 .. 3] do
    words[i] := ResultOfStraightLineProgram(
                    RECOG.ExpressInStd_SL2(sl.bas * cover.lift(std[i])
                                           * sl.basi, fake), Y);
  od;
  return rec( type := type,
              slpstd := CompositionOfStraightLinePrograms(SLPOfElms(words),
                                                          SLPOfElms(sl.all)),
              bas := B, basi := Bi );
end;

# The data for RECOG.Omega_RankOneRewrite in Omega(<d>,q) of type <type>
# with one hyperbolic pair, q = Size(<f>): "O-" with d = 4. With A
# the anisotropic part, the conjugates of t by the powers of delta are
# Siegel transformations F(a): e_1 -> e_1 + a + c f_1, which fix f_1, and
# their conjugates by s are E(a): f_1 -> f_1 + a + c e_1, which fix e_1.
# Both are additive in a in A, and the a of dim_GF(p) A conjugates are a
# basis of A over GF(p), whose inverse `Fbasis` resp. `Ebasis` gives the
# exponents for any a. The stabiliser of e_1 and f_1 is Omega^-(2,q) on A,
# generated by `rot`, the power of delta which fixes e_1; `value` maps it
# into GF(q^2), as in RECOG.Form_RewriteSetup.
RECOG.Omega_RankOneRewriteSetup := function(type, d, f)
  local std, Y, q, p, n, pos, flat, res, k, alpha;

  std := RECOG.ClassicalStandardGenerators(type, d, f);
  Y := GeneratorsWithMemory(List(std.all, x -> ()));
  q := Size(f);
  p := Characteristic(f);
  pos := [3 .. d];
  n := Length(pos) * DegreeOverPrimeField(f);
  # the coordinates over GF(p) of a vector of A
  flat := a -> Concatenation(List(a, x -> Coefficients(CanonicalBasis(f), x)));
  res := rec( rankone := true, count := 0, pos := pos, flat := flat,
              one := One(Y[1]), s := Y[1], smat := std.s,
              delta := Y[3], deltamat := std.delta,
              Fw := List([0 .. n - 1], i -> Y[2]^(Y[3]^-i)),
              Fmat := List([0 .. n - 1], i -> std.t^(std.delta^-i)) );
  res.Ew := List(res.Fw, x -> x^Y[1]);
  res.Emat := List(res.Fmat, x -> x^std.s);
  res.Fbasis := List(res.Fmat, x -> flat(x[1]{pos}))^-1;
  res.Ebasis := List(res.Emat, x -> flat(x[2]{pos}))^-1;
  if type = "O-" then
    k := Order(std.delta[1, 1]);
    if IsEvenInt(q) then
      alpha := Z(q^2);
    else
      alpha := Z(q^2)^((q + 1) / 2);
    fi;
    res.rot := rec( word := Y[3]^k, mat := std.delta^k,
                    value := g -> g[3, 3] + g[3, 4] * alpha );
    res.rot.gen := res.rot.value(res.rot.mat);
  fi;
  return res;
end;

# RECOG.Form_Rewrite for the groups with one hyperbolic pair: e_1 g = x e_1 + y f_1 + a
# with a in A; if x = 0 then a = 0, as A is anisotropic, and s swaps the
# lines of e_1 and f_1. Then F(-a / x) maps e_1 g to x e_1, a power of
# delta to e_1, and E(-a) for f_1 g = f_1 + a + c e_1 maps f_1 g to f_1,
# as the images stay singular. What is left fixes e_1 and f_1, so it is
# a power of W.rot.
RECOG.Omega_RankOneRewrite := function(W, g)
  local word, mult, root, k;

  # g = g0 * word for the input g0
  word := W.one;
  mult := function(w, mat)
    g := g * mat;
    word := word * w;
  end;
  # F(a) or E(a)
  root := function(words, mats, basis, a)
    local c, i;
    c := List(W.flat(a) * basis, IntFFE);
    for i in [1 .. Length(c)] do
      if c[i] <> 0 then
        mult(words[i]^c[i], mats[i]^c[i]);
      fi;
    od;
  end;

  if IsZero(g[1, 1]) then
    mult(W.s, W.smat);
  fi;
  root(W.Fw, W.Fmat, W.Fbasis, -g[1]{W.pos} / g[1, 1]);
  k := LogFFE(g[1, 1], W.deltamat[1, 1]);
  if k = fail then
    return fail;
  fi;
  mult(W.delta^-k, W.deltamat^-k);
  root(W.Ew, W.Emat, W.Ebasis, -g[2]{W.pos});
  if IsBound(W.rot) then
    k := LogFFE(W.rot.value(g), W.rot.gen);
    if k = fail then
      return fail;
    fi;
    mult(W.rot.word^-k, W.rot.mat^-k);
  fi;
  if not IsOne(g) then
    return fail;
  fi;
  return SLPOfElm(word^-1);
end;
