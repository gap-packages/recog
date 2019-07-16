gap> old:=InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);;
gap> gens := GeneratorsOfGroup;;
gap> l := gens(SymmetricGroup(10));;
gap> ll := List(l,x->PermutationMat(x,10)) * Z(5)^0;;
gap> m := GModuleByMats(ll,GF(5));;
gap> s5 := List(ll,x->KroneckerProduct(x,x));;
gap> m := GModuleByMats(s5,GF(5));;
gap> c := MTX.CompositionFactors(m);;
gap> i := Position(List(c,a->a.dimension), 28);;
gap> g := Group(c[i].generators);;
gap> ri := RecognizeGroup(g);;
gap> Size(ri);
3628800
gap> SetInfoLevel(InfoRecog, old);
