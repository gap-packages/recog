#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This files's authors include Daniel Rademacher.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
#############################################################################



#############################################################################
#############################################################################
######## Contains test function for the PhD thesis of the author ############
#############################################################################
#############################################################################



RECOG.GenerateStatictsSL := function(d,q,n,tries)
local H, G, res, bugavoided, hit, counter,e1,e2,gens;

    G := SL(d,q);
    gens := GeneratorsOfGroup(SL(n,q));
    e1 := IdentityMat(d,GF(q));
    e2 := IdentityMat(d,GF(q));
    e1{[1..n]}{[1..n]} := gens[1];
    e2{[1..n]}{[1..n]} := gens[2];

    H := GroupByGenerators([e1,e2]);

    hit := 0;
    counter := 0;

    while counter < tries do
        if RECOG.FindTestEle(H,G,n,"SL") then
            hit := hit + 1;
        fi;
        counter := counter + 1;
    od;

    Display(hit/tries);

    return hit;
end;


RECOG.GenerateStatictsSU := function(d,q,tries)
local H, G, n, res, bugavoided, hit, counter;

    n := 2;
    G := SU(d,q);
    bugavoided := false;
    while not(bugavoided) do
        res := RECOG.FindStdGens_SU(G,d);
        if res[1,1]^res[2] in G then
            bugavoided := true;
        fi;
    od;

    H := GroupByGenerators(res[1]);
    G := G^(res[2]^(-1));

    hit := 0;
    counter := 0;

    while counter < tries do
        if RECOG.FindTestEle(H,G,n,"SU") then
            hit := hit + 1;
        fi;
        counter := counter + 1;
    od;

    Display(hit/tries);

    return hit;
end;


RECOG.GenerateStatictsSU := function(d,q,tries)
local H, G, n, res, bugavoided, hit, counter;

    n := 2;
    G := Sp(d,q);
    bugavoided := false;
    while not(bugavoided) do
        res := RECOG.FindStdGens_Sp(G,d);
        if res[1,1]^res[2] in G then
            bugavoided := true;
        fi;
    od;

    H := GroupByGenerators(res[1]);
    G := G^(res[2]^(-1));

    hit := 0;
    counter := 0;

    while counter < tries do
        if RECOG.FindTestEle(H,G,n,"SU") then
            hit := hit + 1;
        fi;
        counter := counter + 1;
    od;

    Display(hit/tries);

    return hit;
end;


RECOG.FindTestEle := function(H, G, n, type)
local c1, c, t;

    t := PseudoRandom(H);
    c1 := PseudoRandom(G);
    c := t^c1;
    if type = "SL" then
        return RECOG.TestGroupSL(H,c,2*n);
    elif type = "SU" then
        return RECOG.TestGroupSU(H,c,2*n);
    elif type = "Sp" then
        return RECOG.TestGroupSp(H,c,2*n);
    elif type = "Omega" then
        return RECOG.TestGroupOmega(H,c,2*n);
    else
        return fail;
    fi;
end;


RECOG.TestGroupSU := function(G,c,d)
local H, gens, gens2, res;

    gens := List(GeneratorsOfGroup(G),MutableCopyMat);
    gens2 := List(GeneratorsOfGroup(G),MutableCopyMat);
    Apply(gens2,x->x^c);
    Append(gens,gens2);
    H := RECOG.LinearActionRepresentation(GroupByGenerators(gens));
    res := RecogniseClassical(H);
    Display(res);
    if res <> fail and IsBool(res.isSUContained) then
        if res.d = d and res.isSUContained then
            return true;
        else
            return false;
        fi;
    else
        return false;
    fi;
end;



RECOG.TestGroupSL := function(G,c,d)
local H, gens, gens2, res;

    gens := List(GeneratorsOfGroup(G),MutableCopyMat);
    gens2 := List(GeneratorsOfGroup(G),MutableCopyMat);
    Apply(gens2,x->x^c);
    Append(gens,gens2);
    H := RECOG.LinearActionRepresentation(GroupByGenerators(gens));
    res := RecogniseClassical(H);
    #Display(res);
    #if res <> fail and IsBool(res.isSLContained) then
    if res <> fail then
        #if res.d = d and res.isSLContained then
        if res.d = d then
            return true;
        else
            #if res.d = d then

                #Error("here");
            #fi;
            return false;
        fi;
    else
        #Error("here");
        return false;
    fi;
end;



RECOG.TestGroupSp := function(G,c,d)
local H, gens, gens2, res;

    gens := List(GeneratorsOfGroup(G),MutableCopyMat);
    gens2 := List(GeneratorsOfGroup(G),MutableCopyMat);
    Apply(gens2,x->x^c);
    Append(gens,gens2);
    H := RECOG.LinearActionRepresentation(GroupByGenerators(gens));
    res := RecogniseClassical(H);
    Display(res);
    if res <> fail and IsBool(res.isSpContained) then
        if res.d = d and res.isSpContained then
            return true;
        else
            return false;
        fi;
    else
        return false;
    fi;
end;


RECOG.TestGroupOmega := function(G,c,d)
local H, gens, gens2, res;

    gens := List(GeneratorsOfGroup(G),MutableCopyMat);
    gens2 := List(GeneratorsOfGroup(G),MutableCopyMat);
    Apply(gens2,x->x^c);
    Append(gens,gens2);
    H := RECOG.LinearActionRepresentation(GroupByGenerators(gens));
    res := RecogniseClassical(H);
    Display(res);
    if res <> fail and IsBool(res.isSOContained) then
        if res.d = d and res.isSOContained then
            return true;
        else
            return false;
        fi;
    else
        return false;
    fi;
end;
