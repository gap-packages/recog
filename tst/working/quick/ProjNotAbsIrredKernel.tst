gap> START_TEST("ProjNotAbsIrredKernel.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);

# x acts on GF(3)^2 as GF(9)-multiplication, so NotAbsolutelyIrred rewrites
# it as a scalar and its kernel is all of <x> mod scalars, of order 2. These
# seeds make every random kernel element an even power of x. This also
# happened deep inside RecogniseGroup(SO(+1,4,3)).
gap> x := [[0,1],[-1,0]] * Z(3)^0;;
gap> ForAll([2533, 7463, 17734], function(s)
>      local ri;
>      Reset(GlobalRandomSource, s);
>      ri := RecogniseProjectiveGroup(Group(x));
>      return IsReady(ri) and Size(ri) = 2;
>    end);
true

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("ProjNotAbsIrredKernel.tst");
