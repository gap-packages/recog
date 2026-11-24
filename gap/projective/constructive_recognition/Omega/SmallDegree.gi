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
##  Constructive recognition of Omega(5,q), q odd, in its natural
##  representation, by the exceptional isomorphism with Sp(4,q)/<-1>
##  (Kleidman and Liebeck, The subgroup structure of the finite classical
##  groups, 1990, Proposition 2.9.1): the generators are lifted to the
##  covering group, which is recognised by its own code, and the standard
##  generators of Omega are written in those of the covering group.
##
##  The isomorphism comes from the Klein correspondence Omega^+(6,q) =
##  SL(4,q)/<-1> of BaseCase.gi. With w' orthogonal to the space V of
##  Omega(5,q) and Q(w') = -Q(w_1), V + <w'> has type +, and Omega(5,q) is
##  the stabiliser of w' in Omega^+(6,q); its preimage fixes the
##  alternating form which is w' as an element of the exterior square.
##
#############################################################################

# The covering group of Omega(<d>,q) of type <type>, q = Size(<f>): "O" with
# d = 5 and q odd. Returns a record with the following components:
#  - `type`, `field`: the covering group is a conjugate of the group of
#    that type of degree 4 over that field
#  - `lift`: a function which maps a matrix of Omega(d,q), relative to a
#    standard basis, to one of its two preimages, or to fail if it has none
# The standard basis is extended by w', and e_3 = w_1 + w', f_3 = w' - w_1
# is a hyperbolic pair of <w_1, w'>.
RECOG.Omega_SmallDegreeCover := function(type, d, f)
  local q, F, C, res, K, Ki;

  q := Size(f);
  if type = "O" and d = 5 and IsOddInt(q) then
    F := f;
    C := IdentityMat(6, F);
    C[5]{[5, 6]} := [One(F), One(F)];
    C[6]{[5, 6]} := [-One(F), One(F)];
    res := rec( type := "Sp", field := F );
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

# RECOG.FindStdGens_Omega for degree 5: <G> is a group with memory which
# is Omega(5,q), q odd, and <type> is "O". The generators, relative to a
# standard basis B, are lifted to the covering group, a conjugate of
# Sp(4,q), which RECOG.FindStdGens_Sp recognises; the lifts of the
# standard generators of Omega(5,q) are rewritten in the standard
# generators of the covering group, and these words give them in G,
# relative to B.
RECOG.FindStdGens_SmallOmega := function(G, type)
  local f, d, gens, form, B, Bi, cover, A, std, W, words;

  f := FieldOfMatrixGroup(G);
  d := DimensionOfMatrixGroup(G);
  gens := StripMemory(GeneratorsOfGroup(G));
  form := RECOG.ClassicalInvariantForm(type, gens, f);

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
  std := RECOG.FindStdGens_Sp(GroupWithMemory(A));

  W := RECOG.Form_RewriteSetup(cover.type, 4, cover.field);
  words := List(RECOG.ClassicalStandardGenerators(type, d, f).all,
                x -> RECOG.Form_Rewrite(W, std.bas * cover.lift(x)
                                           * std.basi));
  return rec( type := type,
              slpstd := CompositionOfStraightLinePrograms(
                            IntegratedStraightLineProgram(words), std.slpstd),
              bas := B, basi := Bi );
end;
