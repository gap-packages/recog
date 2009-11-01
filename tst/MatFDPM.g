# MatFDPM.g:
# Usage: ReadPackage("recog","tst/MatFDPM.g");
LoadPackage("recog");

# Alternating:
deg := Random(10,88);
g := AlternatingGroup(deg);
f := GF(Random([2,3,4,5,7,9,11]));
gens := List([1..5],x->PseudoRandom(g));
mgens := List(gens,x->PermutationMat(x,deg,f));
m := GModuleByMats(mgens,f);
cf := MTX.CompositionFactors(m);
dims := List(cf,x->x.dimension);
max := Maximum(dims);
pos := Position(dims,max);
x := PseudoRandom(GL(max,f));
mgens := List(cf[pos].generators,y->y^x);
h := Group(mgens);
Print("Testing MatFDPM: ",g,"\n");
ri := RECOG.TestGroup(h,false,Size(g));
Print("\n");

# Symmetric:
deg := Random(10,88);
g := SymmetricGroup(deg);
f := GF(Random([2,3,4,5,7,9,11]));
gens := List([1..5],x->PseudoRandom(g));
mgens := List(gens,x->PermutationMat(x,deg,f));
m := GModuleByMats(mgens,f);
cf := MTX.CompositionFactors(m);
dims := List(cf,x->x.dimension);
max := Maximum(dims);
pos := Position(dims,max);
x := PseudoRandom(GL(max,f));
mgens := List(cf[pos].generators,y->y^x);
h := Group(mgens);
Print("Testing MatFDPM: ",g,"\n");
ri := RECOG.TestGroup(h,false,Size(g));
Print("\n");
