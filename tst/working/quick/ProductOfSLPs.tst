# RECOG.ProductOfStraightLinePrograms replaces
# NewProductOfStraightLinePrograms of the GAP library, which returns a wrong
# product if the first factor assigns to one of its own input slots; see
# https://github.com/gap-system/gap/pull/6891.
#
# `over` is such a factor: on inputs x, y it assigns x*y to slot 1 and then
# x*y^2 to slot 2, which is its result. `first` returns its first input.
gap> over := StraightLineProgram([ [ [ 1, 1, 2, 1 ], 1 ],
>                                  [ [ 1, 1, 2, 1 ], 2 ] ], 2);;
gap> first := StraightLineProgram([ [ 1, 1 ] ], 2);;
gap> a := (1,2);; b := (1,2,3);; c := (4,5);; d := (6,7,8);;
gap> ResultOfStraightLineProgram(over, [ a, b ]) = a * b^2;
true

# Each product is a program in the inputs a, b, c, d (or a, b). The lists
# say from which of these slots a factor reads its two inputs. The first
# case is the one the library function gets wrong.
gap> p := RECOG.ProductOfStraightLinePrograms(over, [ 3, 4 ],
>                                             first, [ 1, 2 ], 4);;
gap> ResultOfStraightLineProgram(p, [ a, b, c, d ]) = (c * d^2) * a;
true
gap> p := RECOG.ProductOfStraightLinePrograms(first, [ 1, 2 ],
>                                             over, [ 3, 4 ], 4);;
gap> ResultOfStraightLineProgram(p, [ a, b, c, d ]) = a * (c * d^2);
true

# Both factors read the same slots: the first must not destroy the inputs
# of the second.
gap> p := RECOG.ProductOfStraightLinePrograms(over, [ 1, 2 ],
>                                             over, [ 1, 2 ], 2);;
gap> ResultOfStraightLineProgram(p, [ a, b ]) = (a * b^2)^2;
true

# The case in which recog met the bug: M10 as a maximal subgroup of M11 in
# dimension 10 over GF(3). For some random states, among them the six
# below, its socle A6 becomes a black-box SL(2,9) leaf in the kernel of a
# node with a non-trivial image. The programs of that leaf assign to their
# input slots, and SLPforElementGeneric multiplies one of them with the
# program of the image. With the library function the program for the
# identity was wrong, so that SLPforElement failed or the tree had the
# wrong size.
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);
gap> g := Group(Z(3)^0 * [
> [ [ 0, 0, 0, 0, 0, 2, 0, 0, 0, 0 ], [ 0, 0, 0, 0, 1, 0, 0, 2, 0, 0 ],
>   [ 2, 0, 2, 0, 0, 1, 0, 0, 0, 0 ], [ 2, 0, 2, 0, 2, 1, 2, 1, 0, 2 ],
>   [ 0, 0, 0, 0, 1, 0, 0, 0, 0, 0 ], [ 2, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
>   [ 2, 0, 0, 0, 2, 1, 2, 0, 0, 0 ], [ 0, 2, 0, 0, 1, 0, 0, 0, 0, 0 ],
>   [ 0, 2, 0, 0, 0, 0, 0, 1, 2, 0 ], [ 1, 2, 1, 2, 1, 2, 1, 0, 0, 0 ] ],
> [ [ 0, 2, 0, 2, 2, 0, 2, 2, 0, 1 ], [ 0, 2, 0, 2, 1, 0, 1, 2, 1, 1 ],
>   [ 0, 2, 0, 2, 1, 0, 1, 0, 1, 0 ], [ 0, 2, 0, 2, 0, 0, 0, 1, 0, 2 ],
>   [ 1, 2, 0, 0, 2, 1, 0, 2, 0, 0 ], [ 1, 0, 1, 1, 0, 2, 1, 0, 0, 2 ],
>   [ 2, 1, 2, 1, 1, 1, 1, 1, 0, 2 ], [ 0, 1, 1, 1, 2, 2, 2, 0, 2, 2 ],
>   [ 1, 2, 2, 1, 2, 2, 2, 0, 2, 2 ], [ 1, 1, 1, 0, 2, 2, 2, 0, 2, 2 ] ] ]);;
gap> ForAll([ 26, 37, 38, 50, 51, 59 ], function(seed)
>   local ri, s;
>   Reset(GlobalMersenneTwister, seed);
>   Reset(GlobalRandomSource, seed);
>   ri := RecogniseGroup(g);
>   s := SLPforElement(ri, One(g));
>   return Size(ri) = 720 and s <> fail
>          and IsOne(ResultOfStraightLineProgram(s, NiceGens(ri)));
> end);
true
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
