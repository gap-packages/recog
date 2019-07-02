# FDPM = fully deleted permutation

# Alternating:
gap> deg := Random(10,88);;
gap> g := AlternatingGroup(deg);;
gap> f := GF(Random([2,3,4,5,7,9,11]));;
gap> gens := List([1..5],x->PseudoRandom(g));;
gap> mgens := List(gens,x->PermutationMat(x,deg,f));;
gap> m := GModuleByMats(mgens,f);;
gap> cf := MTX.CompositionFactors(m);;
gap> dims := List(cf,x->x.dimension);;
gap> max := Maximum(dims);;
gap> pos := Position(dims,max);;
gap> x := PseudoRandom(GL(max,f));;
gap> mgens := List(cf[pos].generators,y->y^x);;
gap> h := Group(mgens);;
gap> ri := RECOG.TestGroup(h,false,Size(g));;

# Symmetric:
gap> deg := Random(10,88);;
gap> g := SymmetricGroup(deg);;
gap> f := GF(Random([2,3,4,5,7,9,11]));;
gap> gens := List([1..5],x->PseudoRandom(g));;
gap> mgens := List(gens,x->PermutationMat(x,deg,f));;
gap> m := GModuleByMats(mgens,f);;
gap> cf := MTX.CompositionFactors(m);;
gap> dims := List(cf,x->x.dimension);;
gap> max := Maximum(dims);;
gap> pos := Position(dims,max);;
gap> x := PseudoRandom(GL(max,f));;
gap> mgens := List(cf[pos].generators,y->y^x);;
gap> h := Group(mgens);;
gap> ri := RECOG.TestGroup(h,false,Size(g));;
