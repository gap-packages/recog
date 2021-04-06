# Classical natural:
# Usage: ReadPackage("recog","tst/testclassicalnatural.g");
LoadPackage("recog");
for q in [2,3,4,5,7,8,9,11,13,16,17,25,81,256] do
  for d in Set([2,3,4,5,6,7,8,9,10,17,18,19,20,29,30,q-1,q,q+1]) do
    if (q > 25 and d >= Maximum(q,10)) or d<=1 then continue; fi;

    h := GL(d,q);
    gens := List([1..10],x->PseudoRandom(h));
    # FIXME: while this is a generating set with HIGH PROBABILITY, it is not always one.
    # This could lead to spurious failures in the test suite...
    g := GroupWithGenerators(gens);
    Print("Testing GL(",d,",",q,") in its natural representation...\n");
    ri := RECOG.TestGroup(g,false,Size(h));
    r := ri;
    if not IsLeaf(ri) then r := ImageRecogNode(ri); fi;
    stamp := r!.fhmethsel.successMethod;
    if stamp="ProjDeterminant" then
        r := KernelRecogNode(r);
        stamp := r!.fhmethsel.successMethod;
    fi;
    Print("Stamp: ",stamp,"\n\n");
  od;
od;
