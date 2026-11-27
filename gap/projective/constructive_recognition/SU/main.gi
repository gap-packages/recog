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
##  Constructive recognition of special unitary groups in their natural
##  representation
##
#############################################################################

# Whether RECOG.FindStdGens_SU goes up by RECOG.SU_DirectGoingUp, in one
# step, instead of RECOG.GoingUp, for even d
RECOG.SU_UseDirectGoingUp := true;

# StandardGenerators of [EHNPR] (see ../GoingDown.gi), 'Outline of the
# algorithm', for SU(d,q0), d >= 4 and q0 <> 2: RECOG.FindStdGensSU4 for
# d = 4, otherwise GoingDown to SU(6,q0) (none for d = 5), FinalDescent
# to SU(4,q0), and GoingUp (see ../GoingUp.gi and DirectGoingUp.gi).
# [EHNPR] also covers q0 = 2, with GoingDown to SU(10,2); here neither the
# final descent nor the base case work for q0 = 2.
# Returns a record with the following components:
#  - `slpstd`: SLP in the generators of <G> for the standard generators of
#    SU(d,q0), as in RECOG.ClassicalStandardGenerators, relative to bas
#  - `bas`: a standard basis for a multiple of the form of <G>, as a matrix
#  - `basi`: its inverse
RECOG.FindStdGens_SU := function(G)
  local f, q, d, down, n, init, slp, bas, up;

  f := FieldOfMatrixGroup(G);
  q := Size(f);
  d := DimensionOfMatrixGroup(G);
  if q = 4 then
    ErrorNoReturn("RECOG.FindStdGens_SU: q0 must not be 2");
  fi;
  if d < 4 then
    ErrorNoReturn("RECOG.FindStdGens_SU: the degree must be at least 4");
  fi;
  if not IsObjWithMemory(GeneratorsOfGroup(G)[1]) then
    G := GroupWithMemory(G);
  fi;

  if d = 4 then
    init := RECOG.FindStdGensSU4(StripMemory(GeneratorsOfGroup(G)), f);
    return rec( slpstd := init.slp, bas := init.bas,
                basi := init.bas^-1 );
  fi;

  if d = 5 then
    down := rec( gens := StripMemory(GeneratorsOfGroup(G)),
                 slp := SLPOfElms(GeneratorsOfGroup(G)),
                 bas := IdentityMat(d, f) );
  else
    Info(InfoRecog_ClassicalNatural, 1, "SU_n: going down in SU(", d, ",",
         RootInt(q, 2), ")");
    down := RECOG.GoingDown(G, "SU", RECOG.GoingDownRandomBound);
  fi;
  n := NrRows(down.gens[1]);
  init := RECOG.SU_FinalDescent(down.gens, f);
  slp := CompositionOfStraightLinePrograms(init.slp, down.slp);
  bas := Concatenation(init.bas * down.bas{[1 .. n]},
                       down.bas{[n + 1 .. d]});

  Info(InfoRecog_ClassicalNatural, 1, "SU_n: going up");
  bas := RECOG.Form_CompleteStandardBasis(G, "SU", bas, 4);
  if RECOG.SU_UseDirectGoingUp and IsEvenInt(d) then
    up := RECOG.SU_DirectGoingUp(G, rec( slp := slp, bas := bas, n := 4 ));
  else
    up := RECOG.GoingUp(G, "SU", rec( slp := slp, bas := bas, n := 4 ));
  fi;
  return rec( slpstd := up.slp, bas := up.bas, basi := up.bas^-1 );
end;
