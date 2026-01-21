# 
gap> START_TEST("PermNiceGens.tst");
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

#
gap> STOP_TEST("PermNiceGens.tst");
