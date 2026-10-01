gap> START_TEST("gh-00302.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);

# Issue #302: A projective tensor-factor image used to miss scalar multiples,
# so this reproducible seed produced a failed KroneckerProduct node.
# See https://github.com/gap-packages/recog/issues/302
gap> z := Z(3^2);;
gap> gens := [ [ [ z^0, z^3, z^7, z^0, z^6, z^5, z^5, z^2 ],
>       [ z^4, z^5, z^6, z^2, z^6, z^3, z^0, z^0 ],
>       [ z^5, 0*z, z^4, z, z^3, 0*z, z^2, z^3 ],
>       [ z, z^7, z^6, z^2, z^3, z^5, z^0, z^0 ],
>       [ z^6, z^5, z^5, z^2, z^0, z^3, z^7, z^0 ],
>       [ z^6, z^3, z^0, z^0, z^4, z^5, z^6, z^2 ],
>       [ z^3, 0*z, z^2, z^3, z^5, 0*z, z^4, z ],
>       [ z^3, z^5, z^0, z^0, z, z^7, z^6, z^2 ] ],
>   [ [ z^5, z^6, z^3, z^5, z^5, z^6, z^3, z^5 ],
>       [ z^3, z^3, z, 0*z, z^7, z^7, z^5, 0*z ],
>       [ z^3, z^4, 0*z, z^5, z^3, z^4, 0*z, z^5 ],
>       [ z^0, z^2, z, z^3, z^4, z^6, z^5, z^7 ],
>       [ z, z^6, z^7, z^5, z^5, z^2, z^3, z ],
>       [ z^7, z^3, z^5, 0*z, z^7, z^3, z^5, 0*z ],
>       [ z^7, z^4, 0*z, z^5, z^3, z^0, 0*z, z ],
>       [ z^4, z^2, z^5, z^3, z^4, z^2, z^5, z^3 ] ] ];;
gap> g := Group(gens);;
gap> i := 13;; Reset(GlobalMersenneTwister, i);; Reset(GlobalRandomSource, i);;
gap> ri := RecogniseGroup(g);;
gap> IsReady(ri);
true

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("gh-00302.tst");
