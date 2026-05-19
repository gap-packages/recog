gap> blocks := [ [ 1 .. 2 ], [ 3 .. 4 ], [ 5 .. 6 ] ];;
gap> lower := IdentityMat(6, GF(3));;
gap> lower[3,1] := Z(3)^0;; lower[5,2] := Z(3)^0;; lower[6,4] := Z(3)^0;;
gap> RECOG.IsBlockLowerTriangularWithBlocks(lower, blocks);
true
gap> upper := StructuralCopy(lower);;
gap> upper[2,3] := Z(3)^0;;
gap> RECOG.IsBlockLowerTriangularWithBlocks(upper, blocks);
false
gap> diag := IdentityMat(6, GF(3));;
gap> RECOG.IsDiagonalBlockOfMatrix(diag, [ 3 .. 4 ]);
true
gap> above := StructuralCopy(diag);;
gap> above[2,3] := Z(3)^0;;
gap> RECOG.IsDiagonalBlockOfMatrix(above, [ 3 .. 4 ]);
false
gap> left := StructuralCopy(diag);;
gap> left[3,2] := Z(3)^0;;
gap> RECOG.IsDiagonalBlockOfMatrix(left, [ 3 .. 4 ]);
false
gap> right := StructuralCopy(diag);;
gap> right[4,5] := Z(3)^0;;
gap> RECOG.IsDiagonalBlockOfMatrix(right, [ 3 .. 4 ]);
false
gap> below := StructuralCopy(diag);;
gap> below[5,4] := Z(3)^0;;
gap> RECOG.IsDiagonalBlockOfMatrix(below, [ 3 .. 4 ]);
false
