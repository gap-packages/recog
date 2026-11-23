#
# BlocksModScalars nodes identify matrices whose diagonal blocks agree up to
# one scalar per block, so SLPs at such a node evaluate on its NiceGens to the
# element only in this sense.
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);
gap> F := GF(5);; z := Z(5);;
gap> a := GeneratorsOfGroup(SL(2, F));; b := GeneratorsOfGroup(SL(3, F));;
gap> g := GroupWithGenerators([
>     DirectSumMat([[z]], z * a[1], b[1]),
>     DirectSumMat([[z^2]], a[2], z^2 * b[2]),
>     DirectSumMat([[z^0]], a[1] * a[2], z * b[1] * b[2]) ]);;
gap> ri := RecognizeGroup(g);;
gap> Size(ri) = Size(g);
true

#
gap> nodes := [];; todo := [ri];;
gap> while todo <> [] do
>     r := Remove(todo);
>     if r!.fhmethsel.successMethod = "BlocksModScalars" then
>         Add(nodes, r);
>     fi;
>     if not IsLeaf(r) then
>         Add(todo, ImageRecogNode(r));
>         if KernelRecogNode(r) <> fail then
>             Add(todo, KernelRecogNode(r));
>         fi;
>     fi;
> od;
gap> nodes <> [];
true

# The top BlocksModScalars node covers all blocks.
gap> r := nodes[1];;
gap> x := MutableCopyMat(One(Grp(r)));;
gap> for i in [1 .. Length(r!.blocks)] do
>     for j in r!.blocks[i] do
>         x[j, j] := z^i;
>     od;
> od;
gap> isone(r)(x);
true
gap> h := GeneratorsOfGroup(Grp(r))[1];;
gap> isone(r)(h);
false
gap> isequal(r)(x * h, h);
true
gap> OrderFunc(r)(x);
1
gap> o := OrderFunc(r)(h);;
gap> isone(r)(h^o) and ForAll(PrimeDivisors(o), p -> not isone(r)(h^(o/p)));
true
gap> OrderFunc(r)(GeneratorsWithMemory([h])[1]) = o;
true

#
gap> SLPWorks := function(r, x)
>     local s;
>     s := SLPforElement(r, x);
>     return s <> fail and
>            isequal(r)(ResultOfStraightLineProgram(s, NiceGens(r)), x);
> end;;
gap> ForAll(nodes, r -> ForAll(GeneratorsOfGroup(Grp(r)), x -> SLPWorks(r, x)));
true
gap> ForAll(nodes, r -> ForAll([1 .. 5], i -> SLPWorks(r, PseudoRandom(Grp(r)))));
true

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
