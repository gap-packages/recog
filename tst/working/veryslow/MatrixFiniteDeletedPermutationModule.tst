# FDPM = fully deleted permutation module
gap> testFDPM := function(deg, field, alternating)
> local old_info_level, g, gens, mgens, m, cf, dims, max, pos, x, new_gens,
>   h, result;
> old_info_level := InfoLevel(InfoRecog);
> if alternating then
>   g := AlternatingGroup(deg);
> else
>   g := SymmetricGroup(deg);
> fi;
> repeat
>   gens := List([1..5],x->PseudoRandom(g));
> until Size(Group(gens)) = Size(g);
> mgens := List(gens,x->PermutationMat(x,deg,field));
> m := GModuleByMats(mgens,field);
> cf := MTX.CompositionFactors(m);
> dims := List(cf,x->x.dimension);
> max := Maximum(dims);
> pos := Position(dims,max);
> x := PseudoRandom(GL(max,field));
> new_gens := List(cf[pos].generators,y->y^x);
> h := Group(new_gens);
> return RECOG.TestGroup(h,false,Size(g));
> end;;

# Smaller dimensions
gap> for deg in [10, 13, 17, 32] do
> for field in List([2,3,4,7,9], GF) do
> testFDPM(deg, field, false);
> testFDPM(deg, field, true);
> od;
> od;

# Big dimension
gap> testFDPM(88, GF(3), false);;
gap> testFDPM(88, GF(2), true);;
