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
##  Constructive recognition of orthogonal groups in their natural
##  representation
##
#############################################################################

# StandardGenerators of [EHNPR] (see ../GoingDown.gi), 'Outline of the
# algorithm', for Omega^+-(d,q), d >= 8 even, and Omega(d,q), d >= 7 odd
# and q odd: GoingDown to Omega^+-(8,q) (none for d = 7), FinalDescent to
# Omega^+(6,q), and GoingUp (see ../GoingUp.gi). [EHNPR] needs d >= 8.
# Degrees 5 and 6 are left
# to RECOG.FindStdGens_SmallOmega, Omega^-(4,q) and Omega(3,q) to
# RECOG.FindStdGens_RankOneOmega; Omega^+(4,q), a central product of two
# SL(2,q), is not supported. The type comes from the parity of d and the
# discriminant resp., for q even, the Arf invariant of the invariant form.
# A FinalDescent which uses up its random selections restarts GoingDown,
# which has no naming test.
# Returns a record with the following components:
#  - `type`: "O+", "O-" or "O"
#  - `slpstd`: SLP in the generators of <G> for the standard generators of
#    Omega(d,q) of that type, as in RECOG.ClassicalStandardGenerators,
#    relative to bas
#  - `bas`: a standard basis for a multiple of the form of <G>, as a matrix
#  - `basi`: its inverse
RECOG.FindStdGens_Omega := function(G)
  local f, d, gens, type, form, down, n, B8, init, slp, bas, up;

  f := FieldOfMatrixGroup(G);
  d := DimensionOfMatrixGroup(G);
  if IsEvenInt(Size(f)) and IsOddInt(d) then
    ErrorNoReturn("RECOG.FindStdGens_Omega: odd degree needs odd q");
  fi;
  if d < 3 then
    ErrorNoReturn("RECOG.FindStdGens_Omega: the degree must be at least 3");
  fi;
  if not IsObjWithMemory(GeneratorsOfGroup(G)[1]) then
    G := GroupWithMemory(G);
  fi;
  gens := StripMemory(GeneratorsOfGroup(G));

  if IsOddInt(d) then
    type := "O";
  else
    type := RECOG.FormOrthogonalType(
                RECOG.ClassicalInvariantForm("O+", gens, f), IdentityMat(d, f));
  fi;
  if d = 4 and type = "O+" then
    ErrorNoReturn("RECOG.FindStdGens_Omega: Omega^+(4,q) is not supported");
  elif d < 5 then
    return RECOG.FindStdGens_RankOneOmega(G, type);
  elif d < 7 then
    return RECOG.FindStdGens_SmallOmega(G, type);
  fi;
  form := RECOG.ClassicalInvariantForm(type, gens, f);

  repeat
    if d > 8 then
      Info(InfoRecog_ClassicalNatural, 1, "Omega_n: going down in ", type, "(",
           d, ",", Size(f), ")");
      down := RECOG.GoingDown(G, type, RECOG.GoingDownRandomBound);
    else
      down := rec( gens := gens, slp := SLPOfElms(GeneratorsOfGroup(G)),
                   bas := IdentityMat(d, f) );
    fi;
    n := Minimum(d, 8);
    B8 := down.bas{[1 .. n]};
    Info(InfoRecog_ClassicalNatural, 1, "Omega_n: base case O+(6,",
         Size(f), ")");
    init := RECOG.Omega_FinalDescent(down.gens, f,
                RECOG.FormRestriction(form, B8), RECOG.GoingDownRandomBound);
  until init <> fail;
  slp := CompositionOfStraightLinePrograms(init.slp, down.slp);
  bas := Concatenation(init.bas * B8, down.bas{[n + 1 .. d]});

  Info(InfoRecog_ClassicalNatural, 1, "Omega_n: going up");
  bas := RECOG.Form_CompleteStandardBasis(G, type, bas, 6);
  up := RECOG.GoingUp(G, type, rec( slp := slp, bas := bas, n := 6 ));
  return rec( type := type, slpstd := up.slp, bas := up.bas,
              basi := up.bas^-1 );
end;
