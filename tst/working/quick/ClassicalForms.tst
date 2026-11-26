gap> START_TEST("ClassicalForms.tst");

# RECOG.ScalarMultipleFrobenius(F, M) returns [1, s] such that M/s
# preserves the hermitian form, also for M with nonzero traces
gap> g := SU(4,5);;
gap> J := InvariantSesquilinearForm(g).matrix;;
gap> isom := m -> m * J * RECOG.TransposedFrobeniusMat(m, 5) = J;;
gap> ForAll(GeneratorsOfGroup(g), m -> ForAll([0..23], function(k)
>      local s;
>      s := RECOG.ScalarMultipleFrobenius(GF(25), Z(25)^k * m);
>      return s[1] = 1 and isom(Z(25)^k * m / s[2]);
>    end));
true

# hence the form of SU(4,5) is found with scalars on its generators
gap> Reset(GlobalRandomSource, 1);; Reset(GlobalMersenneTwister, 1);;
gap> h := Group(Z(25)^3 * g.1, Z(25)^7 * g.2);;
gap> fmodule := RECOG.GeneratorsWithoutScalarsFrobenius(h);;
gap> fmodule.exact;
true
gap> ForAll(MTX.Generators(fmodule.modules[1]), isom);
true
gap> module := GModuleByMats(GeneratorsOfGroup(h), GF(25));;
gap> RECOG.InvariantFormFrobenius(module, fmodule.modules[1])[1];
"unitary"

# and RecogniseClassical names SU(6,5) with scalars on its generators
gap> g := SU(6,5);;
gap> ForAll([1..10], function(i)
>      Reset(GlobalRandomSource, i); Reset(GlobalMersenneTwister, i);
>      return RecogniseClassical(Group(Z(25)^3 * g.1, Z(25)^7 * g.2))
>             .isSUContained = true;
>    end);
true

#
gap> STOP_TEST("ClassicalForms.tst");
