gap> h := GL(3,5^2);;
gap> b := Basis(VectorSpace(GF(5),Elements(GF(5^2))));;
gap> gens := List(GeneratorsOfGroup(h),y->BlownUpMat(b,y));;
gap> g := GroupWithGenerators(gens);;
gap> SetInfoLevel(InfoRecog,0);;
gap> Reset(GlobalRandomSource,10);; Reset(GlobalMersenneTwister,10);;
gap> ri := RecognizeGroup(g);;
gap> ForAll(GeneratorsOfGroup(g), x -> ImageElm(Homom(ri), x) <> fail);
true
gap> mat:=Z(5)^0 * [
>   [ 2, 3, 2, 1, 4, 0 ],
>   [ 1, 1, 0, 1, 4, 0 ],
>   [ 0, 0, 1, 3, 2, 3 ],
>   [ 0, 1, 0, 2, 3, 1 ],
>   [ 0, 1, 2, 0, 2, 2 ],
>   [ 1, 4, 2, 1, 1, 0 ],
> ];;
gap> mat in ri;
false
