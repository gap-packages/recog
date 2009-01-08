# This is A14 mod 3 dim 13 wreath S5:
LoadPackage("cvec");
gens := AtlasGenerators("A14",11).generators;
l := [];
Add(l,CVEC_GlueMatrices([gens[1],gens[1]^0,gens[1]^0,gens[1]^0,gens[1]^0]));
Add(l,CVEC_GlueMatrices([gens[2],gens[1]^0,gens[1]^0,gens[1]^0,gens[1]^0]));
Add(l,KroneckerProduct(PermutationMat((1,2,3,4,5),5,GF(3)),gens[1]^0));
Add(l,KroneckerProduct(PermutationMat((1,2),5,GF(3)),gens[1]^0));
g := Group(l);
