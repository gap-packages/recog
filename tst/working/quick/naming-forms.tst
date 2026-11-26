#
gap> START_TEST("naming-forms.tst");

# H wr S_2 acting on V + V for a group H of 2x2 matrices. The base group is
# reducible, and the characteristic polynomial of an element swapping the two
# summands has only even powers, so it does not reveal the scalar by which
# the element multiplies the form.
gap> Wreath := function(H)
>     local F, one, gens;
>     F := DefaultFieldOfMatrixGroup(H);
>     one := IdentityMat(2, F);
>     gens := List(GeneratorsOfGroup(H), h -> MatrixByBlockMatrix(
>                  BlockMatrix([[1, 1, h], [2, 2, one]], 2, 2)));
>     Add(gens, MatrixByBlockMatrix(BlockMatrix([[1, 2, one], [2, 1, one]], 2, 2)));
>     return Group(gens);
> end;;
gap> WithScalar := G -> Group(Concatenation(GeneratorsOfGroup(G),
>        [PrimitiveRoot(DefaultFieldOfMatrixGroup(G)) * One(G)]));;
gap> HasForm := function(G, type)
>     local r;
>     r := RecogniseClassical(G);
>     return ForAny(r.ClassicalForms, f -> not IsTrivialForm(f) and
>                   IsSesquilinearForm(f) and
>                   ((type = "S" and IsSymplecticForm(f)) or
>                    (type = "U" and IsHermitianForm(f))));
> end;;
gap> ForAll([Wreath(Sp(2, 9)), Wreath(Sp(2, 19))],
>        G -> ForAll([G, WithScalar(G)], H -> HasForm(H, "S")));
true
gap> ForAll([Wreath(GU(2, 3)), Wreath(GU(2, 5))],
>        G -> ForAll([G, WithScalar(G)], H -> HasForm(H, "U")));
true

#
gap> STOP_TEST("naming-forms.tst");
