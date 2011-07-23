SetInfoLevel(InfoRecog,1);   # for silent
SetInfoLevel(InfoRecog,2);   # for progress report
SetInfoLevel(InfoRecog,3);   # for details
g := SL(10,2);
l := List([1..10],x->PseudoRandom(g));
h := GroupWithMemory(l);
r := RECOG.FindStdGens_SL(h,FieldOfMatrixGroup(h));
stdgens := ResultOfStraightLineProgram(r.slpstd,l);
Display(r.bas*stdgens[1]*r.basi);
Print("\n");
Display(r.bas*stdgens[2]*r.basi);
Print("\n");
Display(r.bas*stdgens[3]*r.basi);
Print("\n");
Display(r.bas*stdgens[4]*r.basi);
Print("Lines: ",Length(LinesOfStraightLineProgram(r.slpstd)),"\n");
