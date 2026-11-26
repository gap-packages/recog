gap> m1 := [[2,0,0,0,0,0,0,0,0,0],
>        [0,2,0,0,0,0,0,0,0,0],
>        [1,2,4,0,0,0,0,0,0,0],
>        [2,1,3,1,0,0,0,0,0,0],
>        [2,2,2,0,1,0,0,0,0,0],
>        [1,2,0,0,0,1,0,0,0,0],
>        [0,2,4,2,3,1,3,0,0,0],
>        [2,3,0,1,2,0,0,3,0,0],
>        [1,2,3,1,2,3,1,2,4,0],
>        [2,1,0,2,0,3,4,2,0,4]]*Z(5)^0;;
gap> m2 := [[3,0,0,0,0,0,0,0,0,0],
>        [0,3,0,0,0,0,0,0,0,0],
>        [2,1,4,0,0,0,0,0,0,0],
>        [2,3,1,2,0,0,0,0,0,0],
>        [2,0,4,0,2,0,0,0,0,0],
>        [2,2,2,0,0,2,0,0,0,0],
>        [1,2,3,1,2,3,1,0,0,0],
>        [3,2,1,3,2,1,0,1,0,0],
>        [1,1,1,2,2,2,2,3,2,0],
>        [1,0,3,2,4,4,4,4,0,2]]*Z(5)^0;;
gap> ConvertToMatrixRep(m1);;
gap> ConvertToMatrixRep(m2);;
gap> x := PseudoRandom(GL(10,5));;
gap> gens := [m1^x,m2^x];;
gap> g := GroupWithGenerators(gens);;
gap> ri := RECOG.TestGroup(g,true,61035156250000);;

# In a projective group the kernel of the map onto the diagonal blocks
# consists of scalar multiples of matrices with identity diagonal blocks. The
# scalar is not 1 for these stabilisers of flags in SL(d,q) and GL(d,q), where
# a diagonal block of the SLP found for the image is right only up to scalars.
gap> Elementary := function(d, q, i, j)
>   local m;
>   m := IdentityMat(d, GF(q));
>   m[i,j] := One(GF(q));
>   return m;
> end;;
gap> z := Z(4);;

# blocks of dimension 2 and 1 in SL(3,4)
gap> gens := [ DiagonalMat([z, z^0, z^2]), DiagonalMat([z, z^2, z^0]),
>             [[1,1,0],[1,0,0],[0,0,1]] * z^0, Elementary(3,4,3,1) ];;
gap> ri := RECOG.TestGroup(Group(gens), true, 960);;

# the same in GL(3,4); the recognition used to fail
gap> gens := [ DiagonalMat([z, z^0, z^0]), DiagonalMat([z^0, z^0, z]),
>             [[1,1,0],[1,0,0],[0,0,1]] * z^0, Elementary(3,4,3,1) ];;
gap> ri := RECOG.TestGroup(Group(gens), true, 2880);;

# the same in SL(3,7), over a prime field
gap> gens := [ DiagonalMat(Z(7)^0 * [3,1,5]), [[1,1,0],[0,1,0],[0,0,1]] * Z(7)^0,
>             [[0,1,0],[-1,0,0],[0,0,1]] * Z(7)^0, Elementary(3,7,3,1) ];;
gap> ri := RECOG.TestGroup(Group(gens), true, 32928);;

# three and four blocks of dimension 1: the lower left has several layers
gap> gens := [ DiagonalMat([z, z^2, z^0]), DiagonalMat([z^0, z, z^2]),
>             Elementary(3,4,2,1), Elementary(3,4,3,2) ];;
gap> ri := RECOG.TestGroup(Group(gens), true, 192);;
gap> gens := [ DiagonalMat(Z(5)^0 * [2,3,1,1]), DiagonalMat(Z(5)^0 * [1,2,3,1]),
>             DiagonalMat(Z(5)^0 * [1,1,2,3]), Elementary(4,5,2,1),
>             Elementary(4,5,3,2), Elementary(4,5,4,3) ];;
gap> ri := RECOG.TestGroup(Group(gens), true, 250000);;
