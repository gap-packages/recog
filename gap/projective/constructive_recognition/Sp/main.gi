#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This files's authors include Daniel Rademacher.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
##
##  Constructive recognition of symplectic groups in their natural
##  representation
##
#############################################################################

# StandardGenerators of [EHNPR] (see ../GoingDown.gi), 'Outline of the
# algorithm', for Sp(d,q), d >= 4 and q odd: GoingDown to Sp(8,q) if
# d > 8, FinalDescent to Sp(4,q), and GoingUp (see ../GoingUp.gi).
# [EHNPR] needs d >= 8 and leaves d = 4, 6 to other algorithms ('Small
# degrees'); RECOG.Sp_FinalDescent accepts these degrees as well.
# Returns a record with the following components:
#  - `slpstd`: SLP in the generators of <G> for the standard generators of
#    Sp(d,q), as in RECOG.ClassicalStandardGenerators, relative to bas
#  - `bas`: a standard basis for a multiple of the form of <G>, as a matrix
#  - `basi`: its inverse
RECOG.FindStdGens_Sp := function(G)
  local f, d, down, init, slp, bas, up;

  f := FieldOfMatrixGroup(G);
  d := DimensionOfMatrixGroup(G);
  if not IsObjWithMemory(GeneratorsOfGroup(G)[1]) then
    G := GroupWithMemory(G);
  fi;

  if d > 8 then
    Info(InfoRecog_ClassicalNatural, 1, "Sp_n: going down in Sp(", d, ",",
         Size(f), ")");
    down := RECOG.GoingDown(G, "Sp", RECOG.GoingDownRandomBound);
    init := RECOG.Sp_FinalDescent(down.gens, f);
    slp := CompositionOfStraightLinePrograms(init.slp, down.slp);
    bas := Concatenation(init.bas * down.bas{[1 .. 8]}, down.bas{[9 .. d]});
  else
    init := RECOG.Sp_FinalDescent(StripMemory(GeneratorsOfGroup(G)), f);
    slp := init.slp;
    bas := init.bas;
  fi;

  Info(InfoRecog_ClassicalNatural, 1, "Sp_n: going up");
  bas := RECOG.Form_CompleteStandardBasis(G, "Sp", bas, 4);
  up := RECOG.GoingUp(G, "Sp", rec( slp := slp, bas := bas, n := 4 ));
  return rec( slpstd := up.slp, bas := up.bas, basi := up.bas^-1 );
end;
