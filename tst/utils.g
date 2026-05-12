TestRecogGL := function(d,q)
    local h, gens, g, ri, r, stamp;
    h := GL(d,q);
    gens := List([1..10],x->PseudoRandom(h));
    # FIXME: while this is a generating set with HIGH PROBABILITY, it is not always one.
    # This could lead to spurious failures in the test suite...
    g := GroupWithGenerators(gens);
    ri := RECOG.TestGroup(g,false,Size(h));
    r := ri;
    if not IsLeaf(ri) then r := ImageRecogNode(ri); fi;
    stamp := r!.fhmethsel.successMethod;
    if stamp="ProjDeterminant" then
        r := KernelRecogNode(r);
        stamp := r!.fhmethsel.successMethod;
    fi;
    Print("Stamp: ",stamp,"\n");
    return ri;
end;;
