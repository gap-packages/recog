# Name <grpname>(<param>) 20 times and return the number of wrong answers.
# "unknown" is acceptable in a single run, but the group must be named in at
# least one of them.
TestNaming := function(grpname, param...)
    local expected, G, actual, i, n, failures, target, named;
    failures := 0;
    expected := rec(
        #isGeneric := true,
        isNotAlternating := true,
        isNotExt := true,
        isNotMathieu := true,
        isNotPSL := true,
        isReducible := false,
        isSLContained := false,
        isOmegaContained := false,
        isSpContained := false,
        isSUContained := false,
    );

    if grpname = "SL" or grpname = "GL" then
        target := "isSLContained";
    elif grpname = "SO" or grpname = "GO" or grpname = "Omega" then
        if Length(param) = 2 and IsEvenInt(param[2]) then
            Assert(0, IsOddInt(param[1]));
            target := "isReducible";
        else
            target := "isOmegaContained";
        fi;
    elif grpname = "Sp" then
        target := "isSpContained";
    elif grpname = "SU" or grpname = "GU" then
        target := "isSUContained";
    else
        Error("unsupported group type ", grpname);
    fi;
    expected.(target) := true;

    G := CallFuncList(ValueGlobal(grpname), param);
    named := false;
    for i in [1..20] do
        actual := RecogniseClassical(G);
        if actual.(target) = true then
            named := true;
        fi;
        for n in RecNames(expected) do
            if actual.(n) <> expected.(n) then
                if actual.(n) = "unknown" then
                    continue;
                fi;
                Print(i, ": ", grpname, "(",
                    JoinStringsWithSeparator(List(param, String), ","),
                    ") has bad value for ", n,
                    "; expected ", expected.(n),
                    ", got ", actual.(n), "\n");
                failures := failures + 1;
            fi;
        od;
    od;
    if not named then
        Print(grpname, "(", JoinStringsWithSeparator(List(param, String), ","),
              ") never has ", target, " = true\n");
        failures := failures + 1;
    fi;
    return failures;
end;

# Name each maximal subgroup of the quasisimple classical group of the given
# type (as in ClassicalMaximalsGeneric) 5 times, and return the number of
# subgroups named as the full group. Naming one over a proper subfield is
# right: a subfield subgroup contains the classical group over that field.
# The optional argument is a filter selecting the subgroups to test.
TestNamingMaximals := function(type, d, q, filter...)
    local flag, fieldsize, failures, maxes, k, M, i, ri;
    flag := rec(L := "isSLContained", U := "isSUContained",
                S := "isSpContained", O := "isOmegaContained",
                ("O+") := "isOmegaContained", ("O-") := "isOmegaContained");
    fieldsize := q;
    if type = "U" then
        fieldsize := q^2;
    fi;
    failures := 0;
    maxes := ValueGlobal("ClassicalMaximalsGeneric")(type, d, q);
    if not IsEmpty(filter) then
        maxes := Filtered(maxes, filter[1]);
    fi;
    for k in [1..Length(maxes)] do
        M := maxes[k];
        for i in [1..5] do
            ri := RecogniseClassical(M);
            if ri.(flag.(type)) = true and ri.q = fieldsize then
                Print(type, "(", d, ",", q, "): maximal subgroup ", k,
                      " of order ", Size(M), " is named as the full group\n");
                failures := failures + 1;
                break;
            fi;
        od;
    od;
    return failures;
end;

# The conformal group CGO^+(d,q), q odd: GO^+(d,q) and a similitude with
# non-square multiplier nu, mapping the form F to nu * F, which is isometric
# to F as d is even.
ConformalOrthogonalPlusGroup := function(d, q)
    local G, field, F, nu, B1, B2;
    G := GO(+1, d, q);
    field := GF(q);
    F := InvariantBilinearForm(G).matrix;
    nu := PrimitiveRoot(field);
    B1 := BaseChangeToCanonical(BilinearFormByMatrix(F, field));
    B2 := BaseChangeToCanonical(BilinearFormByMatrix(nu * F, field));
    return ClosureGroup(G, B2^-1 * B1);
end;


# Some maximal subgroups of the conformal group CGO^+(8,5), which
# are particularly tricky for the naming functions
maxes_cgo_plus_8_5 := [
Group(Z(5)^0*[[
    [2,0,0,2,0,4,3,0],
    [1,3,4,1,3,0,0,2],
    [3,3,4,3,4,0,0,1],
    [0,0,0,0,0,1,2,0],
    [1,3,0,0,0,2,4,3],
    [4,0,0,0,0,1,1,0],
    [3,0,0,2,0,2,2,0],
    [0,2,1,4,0,2,4,3],
],[
    [1,0,0,0,0,4,0,0],
    [1,1,0,0,2,4,0,0],
    [3,0,1,2,1,0,1,1],
    [0,0,0,1,0,4,3,0],
    [0,0,0,0,1,3,0,0],
    [0,0,0,0,0,1,0,0],
    [0,0,0,0,0,0,1,0],
    [0,0,0,0,0,2,4,1],
],[
    [1,3,2,0,0,1,1,0],
    [3,4,1,0,0,3,0,4],
    [3,4,1,0,0,0,2,4],
    [0,0,0,1,0,0,0,0],
    [0,0,0,0,1,0,0,0],
    [1,3,0,0,0,1,4,3],
    [4,0,2,0,0,1,3,2],
    [0,1,4,0,0,2,2,1],
],[
    [2,0,0,0,0,1,1,0],
    [0,2,0,3,0,3,0,4],
    [0,0,2,3,0,0,2,4],
    [0,0,0,2,0,0,0,0],
    [3,0,0,0,3,2,2,0],
    [0,0,0,0,0,3,0,0],
    [0,0,0,0,0,0,3,0],
    [0,0,0,2,0,0,0,3],
],[
    [4,2,4,4,2,0,1,0],
    [3,1,1,1,2,1,1,2],
    [4,2,0,3,4,2,1,4],
    [1,2,4,2,3,2,0,1],
    [0,2,3,3,1,4,0,3],
    [0,4,1,1,0,2,2,3],
    [3,0,3,4,4,3,2,0],
    [4,4,0,3,2,4,1,0],
]]),
Group(Z(5)^0*[[
    [2,0,0,4,0,4,3,0],
    [1,3,4,2,4,0,0,2],
    [3,3,4,1,2,0,0,1],
    [0,0,0,0,0,3,1,0],
    [2,1,0,0,0,4,3,1],
    [4,0,0,0,0,1,1,0],
    [3,0,0,4,0,2,2,0],
    [0,2,1,3,0,2,4,3],
],[
    [1,0,0,0,0,4,0,0],
    [1,1,0,0,1,4,0,0],
    [3,0,1,4,3,0,1,1],
    [0,0,0,1,0,2,4,0],
    [0,0,0,0,1,1,0,0],
    [0,0,0,0,0,1,0,0],
    [0,0,0,0,0,0,1,0],
    [0,0,0,0,0,2,4,1],
],[
    [1,3,2,0,0,1,1,0],
    [3,4,1,0,0,3,0,4],
    [3,4,1,0,0,0,2,4],
    [0,0,0,1,0,0,0,0],
    [0,0,0,0,1,0,0,0],
    [1,3,0,0,0,1,4,3],
    [4,0,2,0,0,1,3,2],
    [0,1,4,0,0,2,2,1],
],[
    [2,0,0,0,0,1,1,0],
    [0,2,0,1,0,3,0,4],
    [0,0,2,1,0,0,2,4],
    [0,0,0,2,0,0,0,0],
    [1,0,0,0,3,4,4,0],
    [0,0,0,0,0,3,0,0],
    [0,0,0,0,0,0,3,0],
    [0,0,0,4,0,0,0,3],
],[
    [4,2,4,3,1,0,1,0],
    [3,1,1,2,1,1,1,2],
    [4,2,0,1,2,2,1,4],
    [3,1,2,2,2,1,0,3],
    [0,4,1,2,1,3,0,1],
    [0,4,1,2,0,2,2,3],
    [3,0,3,3,2,3,2,0],
    [4,4,0,1,1,4,1,0],
]]),
Group(Z(5)^0*[[
    [3,3,4,1,0,3,1,0],
    [3,3,4,1,3,0,0,4],
    [4,3,4,3,4,0,0,2],
    [0,0,0,0,0,1,2,0],
    [2,3,0,0,0,2,4,4],
    [0,0,0,0,0,1,1,1],
    [0,0,0,2,0,2,2,2],
    [0,0,0,3,0,1,2,2],
],[
    [1,0,0,0,0,3,1,0],
    [0,1,0,0,2,4,0,4],
    [4,0,1,2,1,0,1,2],
    [0,0,0,1,0,4,3,0],
    [0,0,0,0,1,3,0,0],
    [0,0,0,0,0,1,0,0],
    [0,0,0,0,0,0,1,0],
    [0,0,0,0,0,1,0,1],
],[
    [1,4,1,0,0,3,3,0],
    [1,4,1,0,0,3,0,2],
    [1,4,1,0,0,0,2,2],
    [0,0,0,1,0,0,0,0],
    [0,0,0,0,1,0,0,0],
    [2,3,0,0,0,1,4,4],
    [3,0,2,0,0,1,3,1],
    [0,2,3,0,0,4,4,1],
],[
    [3,0,0,3,0,0,0,0],
    [1,2,0,3,0,3,0,0],
    [1,0,2,3,0,0,2,0],
    [0,0,0,2,0,0,0,0],
    [0,0,0,0,3,2,2,2],
    [0,0,0,0,0,3,0,0],
    [0,0,0,0,0,0,3,0],
    [0,0,0,0,0,4,4,2],
],[
    [0,1,0,2,3,1,4,4],
    [3,1,1,1,2,1,1,2],
    [1,2,0,3,4,2,1,1],
    [4,2,4,2,3,2,0,4],
    [2,2,3,3,1,4,0,0],
    [2,4,1,1,0,2,2,0],
    [0,0,3,4,4,3,2,2],
    [0,3,1,1,3,0,4,4],
]]),
Group(Z(5)^0*[[
    [3,3,4,2,0,3,1,0],
    [3,3,4,2,4,0,0,4],
    [4,3,4,1,2,0,0,2],
    [0,0,0,0,0,3,1,0],
    [4,1,0,0,0,4,3,3],
    [0,0,0,0,0,1,1,1],
    [0,0,0,4,0,2,2,2],
    [0,0,0,1,0,1,2,2],
],[
    [1,0,0,0,0,3,1,0],
    [0,1,0,0,1,4,0,4],
    [4,0,1,4,3,0,1,2],
    [0,0,0,1,0,2,4,0],
    [0,0,0,0,1,1,0,0],
    [0,0,0,0,0,1,0,0],
    [0,0,0,0,0,0,1,0],
    [0,0,0,0,0,1,0,1],
],[
    [1,4,1,0,0,3,3,0],
    [1,4,1,0,0,3,0,2],
    [1,4,1,0,0,0,2,2],
    [0,0,0,1,0,0,0,0],
    [0,0,0,0,1,0,0,0],
    [2,3,0,0,0,1,4,4],
    [3,0,2,0,0,1,3,1],
    [0,2,3,0,0,4,4,1],
],[
    [3,0,0,1,0,0,0,0],
    [1,2,0,1,0,3,0,0],
    [1,0,2,1,0,0,2,0],
    [0,0,0,2,0,0,0,0],
    [0,0,0,0,3,4,4,4],
    [0,0,0,0,0,3,0,0],
    [0,0,0,0,0,0,3,0],
    [0,0,0,0,0,4,4,2],
],[
    [0,1,0,4,4,1,4,4],
    [3,1,1,2,1,1,1,2],
    [1,2,0,1,2,2,1,1],
    [2,1,2,2,2,1,0,2],
    [4,4,1,2,1,3,0,0],
    [2,4,1,2,0,2,2,0],
    [0,0,3,3,2,3,2,2],
    [0,3,1,2,4,0,4,4],
]])
];
