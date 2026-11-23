TestRecogGL := function(d,q)
    local h, gens, g, ri, r, stamp;
    h := GL(d,q);
    # (ab)use product replacement algorithm to get randomized generators
    gens := ProductReplacer(h)!.team;
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
