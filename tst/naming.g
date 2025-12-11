TestNaming := function(grpname, param...)
    local expected, G, actual, i, n;
    expected := rec(
        #isGeneric := true,
        isNotAlternating := true,
        #isNotExt := true,
        isNotMathieu := true,
        #isNotPSL := true,
        isReducible := false,
        #isSLContained := false, # problems with e.g. SO(5,7)
        isOmegaContained := false,
        isSpContained := false,
        isSUContained := false,
    );

    if grpname = "SL" then
        expected.isSLContained := true;
    elif grpname = "SO" then
        if Length(param) = 2 and IsEvenInt(param[2]) then
            Assert(0, IsOddInt(param[1]));
            expected.isReducible := true;
        else
            expected.isOmegaContained := true;
        fi;
    elif grpname = "Sp" then
        expected.isSpContained := true;
    elif grpname = "SU" then
        expected.isSUContained := true;
    else
        Error("unsupported group type ", grpname);
    fi;

    G := CallFuncList(ValueGlobal(grpname), param);
    for i in [1..20] do
        actual := RecogniseClassical(G);
        for n in RecNames(expected) do
            if actual.(n) <> expected.(n) then
                if actual.(n) = "unknown" and expected.(n) <> true then
                    continue;
                fi;
                Print(i, ": ", grpname, "(",
                    JoinStringsWithSeparator(List(param, String), ","),
                    ") has bad value for ", n,
                    "; expected ", expected.(n),
                    ", got ", actual.(n), "\n");
            fi;
        od;
        # TODO: also verify maximal subgroups are *not* recognized as the full
        # group; problem is that the list of MaximalSubgroupClassReps is not
        # (yet) fully available for the classical groups in GAP
        #MaximalSubgroupClassReps
    od;
end;
