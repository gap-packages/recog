# This file is to keep track about how c3c5benchmarks_mats.g was made.

# M11 in GL(10,3):
gens := AtlasGenerators("M11",11).generators;
gl := GL(10,3^5);
x := PseudoRandom(gl);
gens2 := List(gens,y->y^x);;
for i in gens2 do ConvertToMatrixRep(i,3^5); od;
# AppendTo("c3c5benchmarks_mats.g","m11_10_243 := ",gens2,";\n");
# AppendTo("c3c5benchmarks_mats.g",
#          "for i in m11_10_243 do ConvertToMatrixRep(i,3^5); od;\n");

# J2 in GL(13,9):
gens := AtlasGenerators("J2",38).generators;
gl := GL(13,GF(3,10));
x := PseudoRandom(gl);;
gens2 := List(gens,y->y^x);;
# AppendTo("c3c5benchmarks_mats.g","j2_13_59049 := ",gens2,";\n");

# Co3 in GL(22,2):
gens := AtlasGenerators("Co3",7).generators;
gl := GL(22,GF(2,16));
x := PseudoRandom(gl);;
gens2 := List(gens,y->y^x);;
# AppendTo("c3c5benchmarks_mats.g","co3_22_65536 := ",gens2,";\n");

# 2.A8 in GL(24,5):
gens := AtlasGenerators("2.A8",19).generators;
gl := GL(24,GF(5,6));
x := PseudoRandom(gl);;
gens2 := List(gens,y->y^x);;
# AppendTo("c3c5benchmarks_mats.g","2A8_24_15625 := ",gens2,";\n");

# GL(90,2) in GL(90,2^16):
gens := GeneratorsOfGroup(GL(90,2));
gl := GL(90,GF(2,16));
x := PseudoRandom(gl);;
gens2 := List(gens,y->y^x);;
# AppendTo("c3c5benchmarks_mats.g","GL_90_65536 := ",gens2,";\n");

# J2 in GL(14,4):
gens := AtlasGenerators("J2",17).generators;
bas := CanonicalBasis(GF(4));
gens2 := List(gens,x->BlownUpMat(bas,x));;
for i in gens2 do ConvertToMatrixRep(i,2); od;
gl := GL(28,GF(2));
x := PseudoRandom(gl);;
gens2 := List(gens2,y->y^x);;
# AppendTo("c3c5benchmarks_mats.g","J2_28_2 := ",gens2,";\n");

# J2.2 in GL(28,2):
gens := AtlasGenerators("J2.2",3).generators;
gl := GL(28,GF(2));
x := PseudoRandom(gl);
gens2 := List(gens,y->y^x);
# AppendTo("c3c5benchmarks_mats.g","J2_2_28_2 := ",gens2,";\n");

# M22 in GL(45,9):
gens := AtlasGenerators("M22",40).generators;
bas := CanonicalBasis(GF(9));
gens2 := List(gens,x->BlownUpMat(bas,x));;
for i in gens2 do ConvertToMatrixRep(i,3); od;
gl := GL(90,GF(3));
x := PseudoRandom(gl);;
gens2 := List(gens2,y->y^x);;
# AppendTo("c3c5benchmarks_mats.g","M22_90_2 := ",gens2,";\n");

# M24 in GL(23,5):
gens := AtlasGenerators("M24",26).generators;
gens2 := [];
gens2[1] := gens[1]*Z(5,3)^7;
gens2[2] := gens[2]*Z(5,3)^9;
bas := CanonicalBasis(GF(5,3));
gens3 := List(gens2,x->BlownUpMat(bas,x));
for i in gens3 do ConvertToMatrixRep(i,5); od;
m := GModuleByMats(gens3,GF(5));
MTX.IsAbsolutelyIrreducible(m);
c := MTX.FieldGenCentMat(m);
cc := ExtractSubMatrix(c,[1..3],[1..3]);
t := TransformingMats(cc,cc^5);
m := Fold(t[1],3,t);
DeterminantMat(m);   # must be nonzero!
Order(m);            # must be 6
mm := m^2;           # has order 3
n := ZeroMatrix(69,69,gens3[1]);
for i in [1,4..67] do CopySubMatrix(mm,n,[1..3],[i..i+2],[1..3],[i..i+2]); od;
Add(gens3,n);
gl := GL(69,GF(5));
x := PseudoRandom(gl);;
gens3 := List(gens3,y->y^x);;
# AppendTo("c3c5benchmarks_mats.g","M24_69_5 := ",gens3,";\n");

Read("colvaexamples.g");
gens1 := GeneratorsOfGroup(really_good[1]);
gens2 := GeneratorsOfGroup(really_good[2]);
gens3 := GeneratorsOfGroup(really_good[3]);
gens4 := GeneratorsOfGroup(really_good[4]);
f := function(gens1,gens2)
  local gens,i,j;
  gens := [];
  for i in [1..Length(gens1)] do
    for j in [1..Length(gens2)] do
      Add(gens,KroneckerProduct(gens1[i],gens2[j]));
    od;
  od;
  return gens;
end;
gens := f(gens1,gens2);
gens := f(gens,gens3);
gens := f(gens,gens4);
gl := GL(81,19);
x := PseudoRandom(gl);
gens2 := List(gens,y->y^x);
# AppendTo("c3c5benchmarks_mats.g","Grp_3_3_9 := ",gens2,";\n");


DisplayAtlasInfo("J2");
gens := AtlasGenerators("J2",38).generators;
g := Group(gens);
StabilizerChain(g);
f := FrobeniusAutomorphism(GF(9));
gens2 := List(gens,x->List(x,v->List(v,y->y^f)));;
ConvertToMatrixRep(gens2[1],9);
ConvertToMatrixRep(gens2[2],9);
gens2;
m := GModuleByMats(gens,GF(9));
m2 := GModuleByMats(gens2,GF(9));
MTX.IsIrreducible(m);
MTX.IsAbsolutelyIrreducible(m);
MTX.Homomorphisms(m,m2);
bas := CanonicalBasis(GF(9));
gensb := List(gens,x->BlownUpMat(bas,x));
gens2b := List(gens2,x->BlownUpMat(bas,x));
ConvertToMatrixRep(gensb[1],3);
ConvertToMatrixRep(gensb[2],3);
ConvertToMatrixRep(gens2b[2],3);
ConvertToMatrixRep(gens2b[1],3);
m := GModuleByMats(gensb,GF(3));
MTX.IsAbsolutelyIrreducible(m);
MTX.FieldGenCentMat(m);
c := MTX.FieldGenCentMat(m);
ConvertToMatrixRep(c,3);
Display(c);
cc := ExtractSubMatrix(c,[1..2],[1..2]);
ConvertToMatrixRep(cc,3);
t := TransformingMats(cc,cc^3);
m := Fold(t[1],2,t);
DeterminantMat(m);
m*cc*m^-1 = cc;
m*cc*m^-1 = cc^3;
mm := ZeroMutable(gensb[1]);
for i in [1,3..25] do CopySubMatrix(m,mm,[1..2],[i..i+1],[1..2],[i..i+1]); od;
Display(mm);
mm*gensb[1]*mm^-1 = gens2b[1];
mm*gensb[2]*mm^-1 = gens2b[2];
gensf := [];
n := IdentityMatrix(52,t);
CopySubMatrix(gensb[1],n,[1..26],[1..26],[1..26],[1..26]);
Add(gensf,n);
n := IdentityMatrix(52,t);
CopySubMatrix(gensb[2],n,[1..26],[1..26],[1..26],[1..26]);
Add(gensf,n);
n := ZeroMatrix(52,52,t);
CopySubMatrix(One(mm),n,[1..26],[27..52],[1..26],[1..26]);
CopySubMatrix(One(mm),n,[1..26],[1..26],[1..26],[27..52]);
Add(gensf,n);
n := IdentityMatrix(52,t);
CopySubMatrix(mm,n,[1..26],[1..26],[1..26],[1..26]);
#CopySubMatrix(mm,n,[1..26],[27..52],[1..26],[27..52]);
Add(gensf,n);
guck := GModuleByMats(gensf,GF(3));
MTX.IsIrreducible(guck);
g := Group(gensf);
ri := RecogniseGroup(g);
Size(ri);
IsOne(Comm(gensf[1],gensf[3]));
IsOne(Comm(gensf[2],gensf[3]));
n := ZeroMatrix(52,52,t);
CopySubMatrix(One(mm),n,[1..26],[27..52],[1..26],[1..26]);
CopySubMatrix(One(mm),n,[1..26],[1..26],[1..26],[27..52]);
Display(n);
Add(gensf,n);
guck := GModuleByMats(gensf,GF(3));
MTX.IsIrreducible(guck);
ri := RecogniseGroup(Group(gensf));

This exposes one (or two) bugs.
