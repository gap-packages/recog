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

# StandardGenerators of [EHNPR] (see ../GoingDown.gi) for SL(d,q)
RECOG.FindStdGens_SL := function(sld)
  # gens of sld must be gens for SL(d,q) in its natural rep with memory
  # This function runs GoingDown to SL(4,q) and FinalDescent to SL(2,q),
  # and then calls RECOG.SLn_UpStep often enough. Finally it returns an slp
  # such that the SL(d,q) standard generators with respect to the basis
  # bas are expressed by the slp in terms of the original generators of sld.
  local bas,basi,d,down,ext,f,fakegens,init,p,q,sl2stdf,std;

  # Some setup:
  f := FieldOfMatrixGroup(sld);
  p := Characteristic(f);
  q := Size(f);
  ext := DegreeOverPrimeField(f);
  d := DimensionOfMatrixGroup(sld);
  if not IsObjWithMemory(GeneratorsOfGroup(sld)[1]) then
      sld := GroupWithMemory(sld);
  fi;

  # First find an SL4, then an SL2 with the space it acts on:
  Info(InfoRecog_ClassicalNatural,1,"SL_n: going down in SL(",d,",",q,")");
  down := RECOG.GoingDown(sld,"SL",RECOG.GoingDownRandomBound);
  init := RECOG.SLn_FinalDescent(down.gens,f);
  bas := Concatenation(init.bas * down.bas{[1..4]}, down.bas{[5..d]});
  ConvertToMatrixRep(bas,q);
  basi := bas^-1;

  # Now set up fake generators for keeping track what we do:
  fakegens := ListWithIdenticalEntries(Length(GeneratorsOfGroup(sld)),());
  fakegens := GeneratorsWithMemory(fakegens);
  sl2stdf := ResultOfStraightLineProgram(
                 CompositionOfStraightLinePrograms(init.slp,down.slp),
                 fakegens);
  std := rec( f := f, d := d, n := 2, bas := bas, basi := basi,
              sld := sld, sldf := fakegens, slnstdf := sl2stdf,
              p := p, ext := ext );
  Info(InfoRecog_ClassicalNatural,1,"SL_n: going up");
  while std.n < std.d do
      RECOG.SLn_UpStep(std);
  od;
  return rec( slpstd := SLPOfElms(std.slnstdf),
              bas := std.bas, basi := std.basi );
end;
