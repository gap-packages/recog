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
##  Constructive recognition of special unitary groups in their natural
##  representation
##
#############################################################################

# StandardGenerators of [EHNPR] (see ../GoingDown.gi), 'Outline of the
# algorithm', for SU(d,q0), d >= 6 even and q0 odd: GoingDown to SU(6,q0),
# FinalDescent to SU(4,q0), and GoingUp (see ../GoingUp.gi). [EHNPR] also
# covers odd d and even q0; here the GoingUp has neither the standard
# generators x, y of odd degree nor the transvections of even q, and the
# involutions of RECOG.SU_FinalDescent need q0 odd.
# Returns a record with the following components:
#  - `slpstd`: SLP in the generators of <G> for the standard generators of
#    SU(d,q0), as in RECOG.ClassicalStandardGenerators, relative to bas
#  - `bas`: a standard basis for a multiple of the form of <G>, as a matrix
#  - `basi`: its inverse
RECOG.FindStdGens_SU := function(G)
  local f, q, d, down, init, slp, bas, up;

  f := FieldOfMatrixGroup(G);
  q := Size(f);
  d := DimensionOfMatrixGroup(G);
  if IsEvenInt(q) then
    ErrorNoReturn("RECOG.FindStdGens_SU: q must be odd");
  fi;
  if d < 6 or IsOddInt(d) then
    ErrorNoReturn("RECOG.FindStdGens_SU: the degree must be even and at ",
                  "least 6");
  fi;
  if not IsObjWithMemory(GeneratorsOfGroup(G)[1]) then
    G := GroupWithMemory(G);
  fi;

  Info(InfoRecog_ClassicalNatural, 1, "SU_n: going down in SU(", d, ",",
       RootInt(q, 2), ")");
  down := RECOG.GoingDown(G, "SU", RECOG.GoingDownRandomBound);
  init := RECOG.SU_FinalDescent(down.gens, f);
  slp := CompositionOfStraightLinePrograms(init.slp, down.slp);
  bas := Concatenation(init.bas * down.bas{[1 .. 6]}, down.bas{[7 .. d]});

  Info(InfoRecog_ClassicalNatural, 1, "SU_n: going up");
  bas := RECOG.Form_CompleteStandardBasis(G, "SU", bas, 4);
  up := RECOG.GoingUp(G, "SU", rec( slp := slp, bas := bas, n := 4 ));
  return rec( slpstd := up.slp, bas := up.bas, basi := up.bas^-1 );
end;
