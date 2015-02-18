LoadPackage("recog");
Read("~/4.0/pkg/recog/gap/downsp.g");
d := 6;
q := 8;
f := GF(q);
g := Sp(d,q);
x := constructppd2(g,d,q);
l := [x];
Add(l,x^PseudoRandom(g));
Add(l,x^PseudoRandom(g));
h := Group(l);             
id := IdentityMat(6,f);
hh := StabMC(h,id[1],OnRight);
# Size should be 1056706560
if hh.size <> 1056706560 then Error(); fi;
hh := hh.stab;
proj := function(x)
  return ExtractSubMatrix(x,[2..5],[2..5]);
end;
newgens := List(GeneratorsOfGroup(hh),proj);
hhh := Group(newgens);
hom := GroupHomomorphismByFunction(hh,hhh,proj);
hhhm := GroupWithMemory(hhh);
S := StabilizerChain(hhhm);
slpstrong := SLPOfElms(StrongGenerators(S));
strong := ResultOfStraightLineProgram(slpstrong,GeneratorsOfGroup(hh));
ForgetMemory(S);
pullback := function(x)
  local slp;
  slp := SiftGroupElementSLP(S,x).slp;
  return ResultOfStraightLineProgram(slp,strong);
end;
m := [[0,1,0,0],[1,0,0,0],[0,0,0,1],[0,0,1,0]]*Z(2);
ConvertToMatrixRep(m,GF(8));

LoadPackage("recog");
Read("~/4.0/pkg/recog/gap/downsp.g");
d := 10;
q := 2;
f := GF(q);
g := Sp(d,q);
x := constructppd2(g,d,q);
l := [x];
Add(l,x^PseudoRandom(g));
Add(l,x^PseudoRandom(g));
h := Group(l);             
mov := RECOG.MovedSpace(h);
hh := StabMC(h,mov[1],OnRight);
# Size should be 720
if hh.size <> 720 then Error(); fi;
hh := hh.stab;
proj := function(x)
  return ExtractSubMatrix(x,[3..6],[3..6]);
end;
newgens := List(GeneratorsOfGroup(hh),proj);
hhh := Group(newgens);
hom := GroupHomomorphismByFunction(hh,hhh,proj);
hhhm := GroupWithMemory(hhh);
S := StabilizerChain(hhhm);
slpstrong := SLPOfElms(StrongGenerators(S));
strong := ResultOfStraightLineProgram(slpstrong,GeneratorsOfGroup(hh));
ForgetMemory(S);
pullback := function(x)
  local slp;
  slp := SiftGroupElementSLP(S,x).slp;
  return ResultOfStraightLineProgram(slp,strong);
end;
m := [[0,0,1,0],[0,0,0,1],[1,0,0,0],[0,1,0,0]]*Z(2);
ConvertToMatrixRep(m,GF(2));
