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
# degrees'); RECOG.Sp_FinalDescent accepts these degrees as well. For q
# even see RECOG.FindStdGens_SpEven.
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
  if IsEvenInt(Size(f)) then
    return RECOG.FindStdGens_SpEven(G);
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

# RECOG.FindStdGens_Sp for q even and d >= 6, except Sp(6,2), with <G>
# having generators with memory ([EHNPR], 'Outline of the algorithm'):
# GoingDown to Omega^+-(8,q) for the quadratic form which its generators
# preserve (for d = 8 a stingray duo, see RECOG.Sp_EvenDuo8), the
# FinalDescent of orthogonal groups to Omega^+(6,q), and the GoingUp of
# RECOG.Sp_EvenGoingUp; for d = 6, RECOG.Sp_EvenOmega6 in place of the
# first two. A FinalDescent which fails, also for want of a quadratic
# form, restarts GoingDown, which has no naming test.
RECOG.FindStdGens_SpEven := function(G)
  local f, d, gens, form, down, B8, gram, quad, init, slp, bas, up;

  f := FieldOfMatrixGroup(G);
  d := DimensionOfMatrixGroup(G);
  if d < 6 or (d = 6 and Size(f) = 2) then
    ErrorNoReturn("RECOG.FindStdGens_SpEven: needs d >= 6, and q > 2 ",
                  "for d = 6");
  fi;
  gens := StripMemory(GeneratorsOfGroup(G));
  form := RECOG.ClassicalInvariantForm("Sp", gens, f);

  if d = 6 then
    Info(InfoRecog_ClassicalNatural, 1, "Sp_n: base case O+(6,", Size(f),
         ") in Sp(6,", Size(f), ")");
    init := RECOG.Sp_EvenOmega6(gens, f, form);
    slp := init.slp;
    bas := init.bas;
  else
    repeat
      Info(InfoRecog_ClassicalNatural, 1, "Sp_n: going down in Sp(", d, ",",
           Size(f), ")");
      if d > 8 then
        down := RECOG.GoingDown(G, "Sp", RECOG.GoingDownRandomBound);
      else
        down := RECOG.Sp_EvenDuo8(G, f, RECOG.GoingDownRandomBound);
      fi;
      init := fail;
      if down <> fail then
        B8 := down.bas{[1 .. 8]};
        gram := RECOG.FormGram(form, B8);
        quad := RECOG.InvariantQuadraticForm(down.gens, gram, f);
        if quad <> fail then
          Info(InfoRecog_ClassicalNatural, 1, "Sp_n: base case O+(6,",
               Size(f), ")");
          init := RECOG.O_FinalDescent(down.gens, f,
                      rec( gram := gram, frob := 1, field := f, quad := quad ),
                      RECOG.GoingDownRandomBound);
        fi;
      fi;
    until init <> fail;
    slp := CompositionOfStraightLinePrograms(init.slp, down.slp);
    bas := Concatenation(init.bas * B8, down.bas{[9 .. d]});
  fi;

  Info(InfoRecog_ClassicalNatural, 1, "Sp_n: going up");
  bas := RECOG.Form_CompleteStandardBasis(G, "Sp", bas, 6);
  up := RECOG.Sp_EvenGoingUp(G, rec( slp := slp, bas := bas, n := 6 ));
  return rec( slpstd := up.slp, bas := up.bas, basi := up.bas^-1 );
end;
