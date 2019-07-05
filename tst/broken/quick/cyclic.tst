# Gives unexpected error - see issue #123
# Move me to working when you have fixed me please
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
