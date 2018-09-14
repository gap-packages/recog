gap> h := GL(3,5^2);;
gap> b := Basis(VectorSpace(GF(5),Elements(GF(5^2))));;
gap> gens := List(GeneratorsOfGroup(h),y->BlownUpMat(b,y));;
gap> x := PseudoRandom(GL(6,5^3));;
gap> gens := List(gens,y->y^x);;
gap> g := GroupWithGenerators(gens);;

# Remark: The *6 comes from the fact that by blowing up we lose a factor
#         of 6 in scalars, they are now in the projective group.
gap> ri := RECOG.TestGroup(g,true,Size(PGL(3,5^2))*6);;
