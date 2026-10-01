gap> START_TEST("gh-00036.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);

# Issue #36: a diagonal 7x7 group over GF(9) used to miss one BlockScalar
# kernel generator, leading to an underestimated size and failed SLPs.
# See https://github.com/gap-packages/recog/issues/36
gap> z := Z(3^2);;
gap> diags := [
>   [ z^7, z^6, z, z^6, z^3, Z(3)^0, z^5 ],
>   [ z^3, z^5, z^4, z^3, z^2, z^6, z^3 ],
>   [ z^2, z, z^3, z^7, z^5, z^0, z^3 ],
>   [ z, z^7, z^3, z^6, z^4, z^5, z^4 ],
>   [ z^3, z^2, z^0, z^3, z^7, z, z^6 ]
> ];;
gap> g := GroupWithGenerators(List(diags, DiagonalMat));;
gap> i := 157;; Reset(GlobalMersenneTwister, i);; Reset(GlobalRandomSource, i);;
gap> ri := RecognizeGroup(g);;
gap> Size(ri);
16384
gap> ForAll(GeneratorsOfGroup(g), x -> SLPforElement(ri, x) <> fail);
true

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("gh-00036.tst");
