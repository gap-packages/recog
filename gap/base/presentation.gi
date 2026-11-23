#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This file's authors include Torben Wiedemann.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
##
##  This file provides code for standard presentations of some groups
##  (which are not covered by the classicpres package).
##
#############################################################################

# Returns the nice generators of SymmetricGroup(n):
# - Empty list for n=1
# - [(1,2)] for n=2
# - [(1,2), (1,...,n)] for n>2
RECOG.SnNiceGens := function(n)
    local gens;
    if n=1 then
        gens := [];
    else
        gens := [(1,2)];
        if n>2 then
            Add(gens, CycleFromList([1..n])); # n-cycle (1,...,n)
        fi;
    fi;
    return gens;
end;

# Returns the nice generators of AlternatingGroup(n):
# - Empty list for n in [1,2]
# - [(1,2,3)] for n=3
# - [(1,2,3), (3,...,n)] for n>3, n odd
# - [(1,2,3), (1,2)(3,...,n)] for n>3, n even
RECOG.AnNiceGens := function(n)
    local gens, cycle;
    if n in [1,2] then
        gens := [];
    else
        gens := [(1,2,3)];
        if n>3 then
            cycle := CycleFromList([3..n]); # (3,..,n)
            if IsOddInt(n) then
                Add(gens, cycle);
            else
                Add(gens, (1,2)*cycle);
            fi;
        fi;
    fi;
    return gens;
end;

# Returns an SLP `slp` which encodes a set of defining relations of S_n
# on the generators RECOG.SnNiceGens(n) (respecting the order of these generators).
# Thus if F is a free group of rank |RECOG.SnNiceGens(n)| and
# rels := ResultOfStraightLineProgram(slp, GeneratorsOfGroup(F)),
# then there is an isomorphism F / rels -> S_n which maps GeneratorsOfGroup(F)
# to RECOG.SnNiceGens(n) (respecting the order of the generators).
# For n>2, the relations are taken from
# [BLN+03] "A black-box group algorithm for recognizing finite symmetric 
# and alternating groups, I", (2.1).
# For n<=2, an "obvious" presentation of S_n is used.
# Note: The claim in [BLN+03] that this presentation can be found in
# [CM80] "Generators and relations for discrete groups"
# is slightly imprecise. In [CM80, (6.26)],
# the same presentation minus the relations
# s^n = 1 and (t*s)^(n-1) but with the additional weaker relation
# s^n = (t*s)^(n-1) appears. Since this presentation defines S_n by [CM80], we
# can add additional relations that are satisfied in S_n without changing the
# presented group, so the presentation in [BLN+03, (2.1)] is correct.
RECOG.SnRelationsSLP := function(n)
    local F, t, s, rels, j;
    # Edge cases for small n
    if n<1 then
        return fail;
    elif n=1 then
        return []; # no relations necessary
    elif n=2 then
        F := GroupWithMemory(FreeGroup(1));
        return SLPOfElm(F.1^2);
    else
        F := GroupWithMemory(FreeGroup(2));
        t := F.1; # Notation for s and t as in [BLN+03]
        s := F.2;
        rels := [ s^n, t^2, (s*t)^(n-1) ];
        for j in [2..QuoInt(n,2)] do
            Add(rels, (t*s^-j*t*s^j)^2);
        od;
        return SLPOfElms(rels);
    fi;
end;

# Returns a presentation Fp (i.e. an FpGroup) of S_n
# on the generators RECOG.SnNiceGens(n) (respecting the order of these generators)
# using the relations RECOG.SnRelationsSLP.
RECOG.SnPresentation := function(n)
    local F, rels, rel, slp, gens;# s, t, j;
    slp := RECOG.SnRelationsSLP(n); # can be `fail`
    # Edge cases for small n
    if n<1 then
        return fail;
    elif n=1 then
        return FreeGroup(0);
    elif n=2 then
        F := FreeGroup(1);
        gens := GeneratorsOfGroup(F);
        rel := ResultOfStraightLineProgram(slp, gens);
        return F / [rel];
    else
        # Generic case
        F := FreeGroup(2);
        gens := GeneratorsOfGroup(F);
        rels := ResultOfStraightLineProgram(slp, gens);
        return F / rels;
    fi;
end;

# Returns an SLP `slp` which encodes a set of defining relations of A_n
# on the generators RECOG.AnNiceGens(n) (respecting the order of these generators).
# Thus if F is a free group of rank |RECOG.AnNiceGens(n)| and
# rels := ResultOfStraightLineProgram(slp, GeneratorsOfGroup(F)),
# then there is an isomorphism F / rels -> A_n which maps GeneratorsOfGroup(F)
# to RECOG.AnNiceGens(n) (respecting the order of the generators).
# For n>3, the relations are taken from
# [CM] "Generators and Relations for Discrete Groups", Fourth Edition, 1980,
# Coxeter-Moser, section 6.4, relations cited from Carmichael 1923, p. 262.
# For n<=3, an "obvious" presentation of A_n is used.
# For odd n, this is the same presentation as in
# [BLN+03] "A black-box group algorithm for recognizing finite symmetric 
# and alternating groups, I", (2.2).
# For even n, it is nearly the same presentation as in [BLN+03], (2.3), but some
# relations are erronously missing in [BLN+03], (2.3).
RECOG.AnRelationsSLP := function(n)
    local F, rels, s, t, k;
    # Edge cases for small n
    if n<1 then
        return fail;
    elif n=1 or n=2 then
        return []; # no relations
    elif n=3 then
        F := GroupWithMemory(FreeGroup(1));
        return SLPOfElm(F.1^3);
    else
        # Generic case
        F := GroupWithMemory(FreeGroup(2));
        t := F.1; # Notation for s and t as in [BLN+03]
        s := F.2;
        rels := [ s^(n-2), t^3 ];
        if IsOddInt(n) then
            Add(rels, (s*t)^n);
            for k in [1..QuoInt(n-3, 2)] do
                Add(rels, (t*s^(-k)*t*s^k)^2);
            od;
        else
            Add(rels, (s*t)^(n-1));
            # The following relations appear in [CM80], but not in [BLN+03]
            # (except for the case k=1, which appears in [BLN+03])
            for k in [1..QuoInt(n-2, 2)] do
                Add(rels, (t^((-1)^k)*s^(-k)*t*s^k)^2);
            od;
        fi;
        return SLPOfElms(rels);
    fi;
end;

# Returns a presentation Fp (i.e. an FpGroup) of A_n
# on the generators RECOG.AnNiceGens(n) (respecting the order of these generators)
# using the relations RECOG.AnRelationsSLP.
RECOG.AnPresentation := function(n)
    local F, rels, rel, slp, gens;
    slp := RECOG.AnRelationsSLP(n); # can be `fail`
    # Edge cases for small n
    if n<1 then
        return fail;
    elif n=1 or n=2 then
        return FreeGroup(0);
    elif n=3 then
        F := FreeGroup(1);
        gens := GeneratorsOfGroup(F);
        rel := ResultOfStraightLineProgram(slp, gens);
        return F / [rel];
    else
        # Generic case
        F := FreeGroup(2);
        gens := GeneratorsOfGroup(F);
        rels := ResultOfStraightLineProgram(slp, gens);
        return F / rels;
    fi;
end;
