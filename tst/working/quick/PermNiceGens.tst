# 
gap> START_TEST("PermNiceGens.tst");

####### Test NiceGeneratorsSn ########
gap> testNiceGeneratorsSn := function(grp)
>  local Sn, m, niceGens, fullCycle, transp, cyclen1, x, y, i;
>  m := Size(MovedPoints(grp));
>  niceGens := RECOG.NiceGeneratorsSn(grp, 10000);
>  if m<=2 then
>    if niceGens = fail then
>      return; # everything ok
>    else
>      Display("NiceGeneratorsSn should return fail for n<=2");
>    fi;
>  elif niceGens <> fail then
>    fullCycle := niceGens[1];
>    transp := niceGens[2];
>    if Size(MovedPoints(transp)) <> 2 then
>      Display("Second generator is not a transposition");
>    fi;
>    cyclen1 := CycleStructurePerm(niceGens[1]);
>    for i in [1..m-2] do
>      if IsBound(cyclen1[i]) then
>        Display("First generator is not a full cycle");
>      fi;
>    od;
>    x := MovedPoints(transp)[1];
>    y := MovedPoints(transp)[2];
>    if not (x^fullCycle = y or y^fullCycle = x) then
>      Display("Transposition does not interchange successive points of full cycle");
>    fi;
>  fi;
> end;;

# Test that NiceGeneratorsSn finds correct generators
gap> for n in [1..50] do
>  Sn := SymmetricGroup(n);
>  for j in [1..3] do # Test a few times
>    testNiceGeneratorsSn(Sn);
>    testNiceGeneratorsSn(Group(Random(Sn), Random(Sn)));
>  od;
> od;

# Test that NiceGeneratorsSn returns fail for some groups that
# are not a full symmetric group
gap> grps := [Group((1,2,3)), Group((1,2), (3,4)), Group((1,10),(2,15,30))];;
gap> for G in grps do if RECOG.NiceGeneratorsSn(G, 10000) <> fail then
>  Print("NiceGeneratorsSn should not succeed for ", G, "\n");
> fi; od;

####### Test NiceGeneratorsAn ########
gap> testNiceGeneratorsAn := function(grp)
>  local m, niceGens, longPerm, shortPerm, cyclenShort, cyclenLong;
>  m := Size(MovedPoints(grp));
>  if IsOddInt(m) then
>    niceGens := RECOG.NiceGeneratorsAnOdd(grp, 10000);
>  else
>    niceGens := RECOG.NiceGeneratorsAnEven(grp, 10000);
>  fi;
>  if niceGens <> fail then
>    longPerm := niceGens[1];
>    shortPerm := niceGens[2];
>    cyclenShort := CycleStructurePerm(shortPerm);
>    cyclenLong := CycleStructurePerm(longPerm);
>    if IsOddInt(m) then
>      if ForAny(Union([1], [3..m]), i->IsBound(cyclenShort[i])) or cyclenShort[2] <> 1 then
>        Display("Short permutation is not a 3-cycle for m odd");
>      fi;
>      if ForAny([1..m-4], i->IsBound(cyclenLong[i])) or cyclenLong[m-3] <> 1 then
>        Display("Long permutation is not an (m-2)-cycle for m odd");
>      fi;
>      if Size(Intersection(MovedPoints(longPerm), MovedPoints(shortPerm))) <> 1 then
>        Display("Supports of 3-cycle and (m-2)-cycle do not intersect in one point for m odd");
>      fi;
>    fi;

# TODO: Test for even m is still missing
>  fi;
> end;;

# Test that NiceGeneratorsAn works for AlternatingGroup
gap> for m in [3..5] do
>  testNiceGeneratorsAn(AlternatingGroup(m));
> od;

# Test that NiceGeneratorsAn returns fail for some non-alternating groups
gap> for G in [Group((1,2,3,4)), Group((1,2),(3,4)), Group((1,2,3,4), (5,6,7))] do
>  if RECOG.NiceGeneratorsAnEven(G, 1000) <> fail or RECOG.NiceGeneratorsAnOdd(G, 1000) <> fail then
>    Display("Group is not alternating");
>  fi; od;

#
gap> STOP_TEST("PermNiceGens.tst");
