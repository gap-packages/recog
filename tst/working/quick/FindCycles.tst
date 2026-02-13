# 
gap> START_TEST("FindCycles.tst");
gap> testFindCyclesNoFail := function(G, lenList, N)
>  local cycles, n, i, cyclen, j;
>  cycles := RECOG.FindCycles(G, lenList, N);
>  n := Length(MovedPoints(G));
>  if cycles = fail then
>    Display("Error");
>  fi;
>  for i in [1..Length(lenList)] do
>    cyclen := CycleStructurePerm(cycles[i]);
>    for j in [2..n] do
>      if j <> lenList[i] and IsBound(cyclen[j-1]) then
>        Display("Result contains a cycle of incorrect length");
>      elif j = lenList[i] and IsBound(cyclen[j-1]) and cyclen[j-1] <> 1 then
>        Display("Result is not a cycle of correct length");
>      fi;
>    od;
>  od;
> end;;
gap> testFindCyclesFail := function(G, lenList, N)
>  local cycles;
>  cycles := RECOG.FindCycles(G, lenList, N);
>  if cycles <> fail then
>    Display("We found a cycle which does not lie in the input group");
>  fi;
> end;;

# Test groups where we should find all cycles (with very high probability)
gap> for i in [1..5] do
>  testFindCyclesNoFail(SymmetricGroup(3), [2,3], 10000);
>  testFindCyclesNoFail(SymmetricGroup(5), [3,5], 10000);
>  testFindCyclesNoFail(SymmetricGroup(10), [2,3,5,7,10], 10000);
>  testFindCyclesNoFail(SymmetricGroup(53), [3,11,23,53], 10000);
>  testFindCyclesNoFail(AlternatingGroup(3), [3], 10000);
>  testFindCyclesNoFail(AlternatingGroup(5), [3,5], 10000);
>  testFindCyclesNoFail(AlternatingGroup(10), [3,5,7], 10000);
>  testFindCyclesNoFail(AlternatingGroup(53), [3,11,23,53], 10000);
> od;

# Test groups where no cycle of the desired length exists
gap> testFindCyclesFail(AlternatingGroup(5), [2], 10000);
gap> testFindCyclesFail(AlternatingGroup(55), [2], 10000);
gap> testFindCyclesFail(Group((1,2,3,4,5)), [3], 10000);
gap> testFindCyclesFail(Group((1,2,3,4,5)), [4], 10000);
gap> testFindCyclesFail(Group((1,2,3)), [2], 10000);

#
gap> STOP_TEST("PermNiceGens.tst");
