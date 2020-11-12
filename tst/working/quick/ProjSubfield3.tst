gap> h := GL(3,3^2);;
gap> x := PseudoRandom(GL(3,3^4));;
gap> gens := List(GeneratorsOfGroup(h),y->y^x);;
gap> gens[1] := gens[1] * Z(3^4);;
gap> gens[2] := gens[2] * Z(3^4)^17;;
gap> g := GroupWithGenerators(gens);;

# Remark: The *4 comes from the fact that by blowing up we lose a factor
#         of 4 in scalars, they are now in the projective group.
gap> level := InfoLevel(InfoOrb);;
gap> SetInfoLevel(InfoOrb, 0);;
gap> ri := RECOG.TestGroup(g,true,Size(PGL(3,3^2)));;
gap> SetInfoLevel(InfoOrb, level);;
