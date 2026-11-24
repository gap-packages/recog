# Issue #123: an imprimitive group over GF(19^3), a field without compressed
# matrices. C3C5 acts on the two blocks, and that homomorphism has to return
# fail for the elements outside the group which RECOG.TestGroup feeds it.
gap> G := Group(Z(19^3) * [
>     [ [ Z(19^3)^254, 0 ], [ 0, Z(19^3)^254 ] ],
>     [ [ Z(19^3)^762, 0 ], [ 0, Z(19^3)^6096 ] ],
>     [ [ Z(19^3)^54, 0 ], [ 0, Z(19^3)^54 ] ],
>     [ [ 0, 1 ], [ 1, 0 ] ],
>     [ [ 1, 0 ], [ 0, Z(19^3)^3429 ] ],
>     [ [ Z(19^3)^3429, 0 ], [ 0, 1 ] ]
> ]);;

#
gap> ri := RECOG.TestGroup(G, false, 246888);;
