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
# algorithm', for Omega^+-(d,q), d >= 8 even, and Omega(d,q), d >= 9 odd, q
# odd: GoingDown to Omega^+-(8,q), FinalDescent to Omega^+(6,q), and GoingUp
# (see ../GoingUp.gi). The type comes from the parity of d and the
# discriminant of the invariant form. A FinalDescent which uses up its
# random selections restarts GoingDown, which has no naming test. [EHNPR]
# also covers even q.
# Returns a record with the following components:
#  - `type`: "O+", "O-" or "O"
#  - `slpstd`: SLP in the generators of <G> for the standard generators of
#    Omega(d,q) of that type, as in RECOG.ClassicalStandardGenerators,
#    relative to bas
#  - `bas`: a standard basis for a multiple of the form of <G>, as a matrix
#  - `basi`: its inverse
RECOG.FindStdGens_O := function(G)
  local f, d, gens, type, form, down, B8, init, slp, bas, up;

  f := FieldOfMatrixGroup(G);
  d := DimensionOfMatrixGroup(G);
  if IsEvenInt(Size(f)) then
    ErrorNoReturn("RECOG.FindStdGens_O: q must be odd");
  fi;
  if d < 8 then
    ErrorNoReturn("RECOG.FindStdGens_O: the degree must be at least 8");
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
  form := RECOG.ClassicalInvariantForm(type, gens, f);

  repeat
    if d > 8 then
      Info(InfoRecog_ClassicalNatural, 1, "O_n: going down in ", type, "(",
           d, ",", Size(f), ")");
      down := RECOG.GoingDown(G, type, RECOG.GoingDownRandomBound);
    else
      down := rec( gens := gens, slp := SLPOfElms(GeneratorsOfGroup(G)),
                   bas := IdentityMat(d, f) );
    fi;
    B8 := down.bas{[1 .. 8]};
    Info(InfoRecog_ClassicalNatural, 1, "O_n: base case O+(6,", Size(f), ")");
    init := RECOG.O_FinalDescent(down.gens, f,
                rec( gram := RECOG.FormGram(form, B8), frob := 1, field := f ),
                RECOG.GoingDownRandomBound);
  until init <> fail;
  slp := CompositionOfStraightLinePrograms(init.slp, down.slp);
  bas := Concatenation(init.bas * B8, down.bas{[9 .. d]});

  Info(InfoRecog_ClassicalNatural, 1, "O_n: going up");
  bas := RECOG.Form_CompleteStandardBasis(G, type, bas, 6);
  up := RECOG.GoingUp(G, type, rec( slp := slp, bas := bas, n := 6 ));
  return rec( type := type, slpstd := up.slp, bas := up.bas,
              basi := up.bas^-1 );
end;
