#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This files's authors include Max Neunhöffer, Ákos Seress.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
#############################################################################

# SLP in the standard generators of RECOG.MakeSL_StdGens(p,ext,2,2) for
# those of RECOG.ClassicalStandardGenerators("SL", 2, <f>): t = E(1,2,1),
# s = E(1,2,1) E(2,1,-1) E(1,2,1) and delta, a product of elementary
# matrices; v and x are the identity.
RECOG.SL2_FromMakeSLStdGens := function(f)
  local ext, recog, gens, upper, lower, basis, E, one, t, s, delta;

  ext := DegreeOverPrimeField(f);
  recog := RECOG.MakeSL_StdGens(Characteristic(f), ext, 2, 2);
  gens := GeneratorsWithMemory(recog.all);
  upper := gens{[1 .. ext]};
  lower := gens{[ext + 1 .. 2 * ext]};
  basis := Basis(f, List([0 .. ext - 1], k -> Z(Size(f))^k));

  # E(1, 2, lambda) and E(2, 1, lambda) from those with lambda in the basis
  E := function(i, j, lambda)
    local words;
    if i = 1 then
      words := upper;
    else
      words := lower;
    fi;
    return Product(ListN(words, List(Coefficients(basis, lambda), IntFFE),
                         \^));
  end;

  one := gens[1]^0;
  t := E(1, 2, One(f));
  s := t * E(2, 1, -One(f)) * t;
  delta := RECOG.SL_ExpressByElementary(
               RECOG.ClassicalStandardGenerators("SL", 2, f).delta, E, one);
  return SLPOfElms([s, t, delta, one, one]);
end;

# Algorithm StandardGenerators of [EHNPR] (see ../GoingDown.gi), Section
# 'Outline of the algorithm', for SL(d,q), d >= 3: GoingDown to SL(4,q)
# (none for d = 3), FinalDescent to SL(2,q) as in [HNPR24] (see
# BaseCase.gi), and GoingUp (see ../GoingUp.gi). It takes no bounds on
# random selections and does not return fail, as its three parts retry
# until they succeed.
# The standard generators are those of RECOG.ClassicalStandardGenerators;
# those of the SL(2,q) are translated from RECOG.MakeSL_StdGens, which
# RECOG.SL_FinalDescent returns.
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
  slp := CompositionOfStraightLinePrograms(RECOG.SL2_FromMakeSLStdGens(f),
                                           slp);
  bas := Concatenation(init.bas * down.bas{[1 .. n]}, down.bas{[n + 1 .. d]});

  Info(InfoRecog_ClassicalNatural, 1, "SL_n: going up");
  up := RECOG.GoingUp(sld, "SL", rec( slp := slp, bas := bas, n := 2 ));
  return rec( slpstd := up.slp, bas := up.bas, basi := up.bas^-1 );
end;
