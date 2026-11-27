#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This file's authors include Max Neunhöffer, Ákos Seress.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
#############################################################################

# Algorithm StandardGenerators of [EHNPR] (see ../GoingDown.gi), Section
# 'Outline of the algorithm', for SL(d,q), d >= 3: GoingDown to SL(4,q)
# (none for d = 3), FinalDescent to SL(2,q) as in [HNPR24] (see
# BaseCase.gi), and GoingUp (see ../GoingUp.gi). It takes no bounds on
# random selections and does not return fail, as its three parts retry
# until they succeed.
# The standard generators are those of RECOG.ClassicalStandardGenerators.
# The generators of <sld> must have memory, or sld is replaced by a group
# with memory.
# Returns a record with the following components:
#  - `slpstd`: SLP in the generators of <sld> for the standard generators
#    of RECOG.ClassicalStandardGenerators("SL", d, f) relative to bas
#  - `bas`: that basis, as a matrix
#  - `basi`: its inverse
RECOG.FindStdGens_SL := function(sld)
  local f, d, down, n, init, slp, bas, up;

  f := FieldOfMatrixGroup(sld);
  d := DimensionOfMatrixGroup(sld);
  if not IsObjWithMemory(GeneratorsOfGroup(sld)[1]) then
    sld := GroupWithMemory(sld);
  fi;

  if d = 3 then
    down := rec( gens := StripMemory(GeneratorsOfGroup(sld)),
                 slp := SLPOfElms(GeneratorsOfGroup(sld)),
                 bas := IdentityMat(d, f) );
  else
    Info(InfoRecog_ClassicalNatural, 1, "SL_n: going down in SL(", d, ",",
         Size(f), ")");
    down := RECOG.GoingDown(sld, "SL", RECOG.GoingDownRandomBound);
  fi;
  n := NrRows(down.gens[1]);
  init := RECOG.SL_FinalDescent(down.gens, f);
  slp := CompositionOfStraightLinePrograms(init.slp, down.slp);
  bas := Concatenation(init.bas * down.bas{[1 .. n]}, down.bas{[n + 1 .. d]});

  Info(InfoRecog_ClassicalNatural, 1, "SL_n: going up");
  up := RECOG.GoingUp(sld, "SL", rec( slp := slp, bas := bas, n := 2 ));
  return rec( slpstd := up.slp, bas := up.bas, basi := up.bas^-1 );
end;
