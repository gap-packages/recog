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
######## Constructive recognition SU(4,q) in natural representation #########
#############################################################################
#############################################################################


# The code here is from Brooksbank and Clarksen
# Note that the papers are not correct and we have to modify a lot in order to get the functions running
# We mark every point, where we differ from the paper



RECOG.ConstructiveRecognitionSU4NaturalRepresentation := function(G, q, epsilon)

     # TODO: Needs SU3

end;



RECOG.IsMersennePrimeNumber := function(p)
local i;

    i := 0;
    while 2^i-1 <= p do
        if p = 2^i-1 then
            return true;
        fi;
        i := i + 1;
    od;

    return false;

end;



RECOG.IsFermat := function(p)
local F;

    F := List([0..4], i -> 2^(2^i)+1 );
    return p in F;

end;



RECOG.IsPowerOfTwo := function(j)
local SmallPowersOfTwo;

    SmallPowersOfTwo := List([1..100], i -> 2^i );
    return j in SmallPowersOfTwo;

end;



RECOG.IsSpecialPPDElement:=function(a,F,j,p,n)

    if n = 1 then
        if RECOG.IsFermat(p) then
            return ((j mod 4) = 0);
        else
            return RECOG.IsPowerOfTwo(j);
        fi;
    else
        if p = 2 and n = 6 then
            if j mod 21 = 0 then
                return true;
            else
                return false;
            fi;
        elif n = 2 and RECOG.IsMersennePrimeNumber(p) then
            if j mod 4 = 0 then
                return true;
            else
                return false;
            fi;
        else
            if IsPpdElement(F,a,2,p,n/2) <> false then
                return true;
            fi;
        fi;
    fi;

    return false;

end;




# TODO: Deal with even characteristic
# TODO: Avoid computing Order (ask Alice!)
# Input: natural < X > = SU(3,q)
# Output: standard generators of SU(3,q) as words in X
RECOG.RecogniseNaturalSU3:=function(G, q)
local p, s, F, i, a, k, fact, DivisorOrder, found, ord, b, H, L, LL, g, moveToSL, module, res, t;

    fact := Factors(q);
    p := fact[1];
    k := Size(fact);
    s := RECOG.FindSForSLSUIsomorphism(q);
    F := GF(q^2);

    i := 1;
    found := false;
    while i < 10 do
        t := PseudoRandom(G);
        a := t^(2*(q-1));
        ord := Order(t);
        if RECOG.IsSpecialPPDElement(t,F,ord,p,2*k) and RECOG.IsSpecialPPDElement(t,F,ord,p,k) then
            found := true;
            break;
        fi;
        i := i + 1;
    od;

    if not(found) then
        return TemporaryFailure;
    fi;

    i := 1;
    found := false;
    while i < 10 do
        g := PseudoRandom(G);
        b := a^g;
        H := GroupByGenerators([a,b]);
        L := RECOG.DerivedSubgroupMonteCarlo(H,20);
        module := GModuleByMats(GeneratorsOfGroup(L), F);
        if not(MTX.IsIrreducible(module)) and Size(L) = Size(SL(2,q)) then
            LL := RECOG.LinearActionRepresentation(L);
            moveToSL := List(GeneratorsOfGroup(LL),x->RECOG.IsomorphismFromSU2ToSL2(x,q,s));
            Error("here");
            res := RECOG.ConstructiveRecognitionSL2NaturalRepresentation(GroupByGenerators(moveToSL),q,0.001);
            res := RECOG.ConstructiveRecognitionSL2NaturalRepresentationCompleteBasis(res,GF(q),q,p,k/2);
        fi;
        i := i + 1;
    od;

    if not(found) then
        Display("nichts gefunden");
        Error("here");
    fi;

    Error("here");

end;



RECOG.FindSForSLSUIsomorphism := function(q)
local a;

    a := PrimitiveElement(GF(q^2));
    return a^q-a;

end;



RECOG.IsomorphismFromSU2ToSL2:=function(g,q,s)
local mat;

    mat := IdentityMat(2,GF(q));
    mat[1,1] := g[1,1];
    mat[2,2] := g[2,2];
    mat[1,2] := s*g[1,2];
    mat[2,1] := s^(-1)*g[2,1];
    return mat;

end;



RECOG.IsomorphismFromSL2ToSU2:=function(g,q,s)
local mat;

    mat := IdentityMat(2,GF(q));
    mat[1,1] := g[1,1];
    mat[2,2] := g[2,2];
    mat[1,2] := s^(-1)*g[1,2];
    mat[2,1] := s*g[2,1];
    return mat;

end;