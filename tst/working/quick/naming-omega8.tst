#
gap> START_TEST("naming-omega8.tst");

# Omega^+(8,2) is named from the size of its projective action. A stabiliser
# chain computed with random := 200 is too small about once in 500 runs, and
# Omega^+(8,2) was then reported not to be contained. With GAP 4.17dev these
# seeds reproduce it within 5 calls each.
gap> oldMT := State(GlobalMersenneTwister);;
gap> oldRS := State(GlobalRandomSource);;
gap> gens := GeneratorsOfGroup(Omega(1, 8, 2));;
gap> ForAny([304, 456, 459, 512], function(s)
>        local G;
>        Reset(GlobalMersenneTwister, s);
>        Reset(GlobalRandomSource, s);
>        G := Group(gens);
>        return ForAny([1 .. 5],
>                      i -> RecogniseClassical(G).isOmegaContained = false);
>    end);
false
gap> Reset(GlobalMersenneTwister, oldMT);;
gap> Reset(GlobalRandomSource, oldRS);;

#
gap> STOP_TEST("naming-omega8.tst");
