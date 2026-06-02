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



###################################################################################################
###################################################################################################
######## Order algorithms #########################################################################
###################################################################################################
###################################################################################################


# All the functions below can also be adjustet for permutation groups. For more details see Magma.

# TODO: Implement next function
RECOG.IsScalarMatrix := function(g)
local i, j, d, scalar, fld, zero;

    d := NumberRows(g);
    fld := FieldOfMatrixList([g]);
    zero := Zero(fld);

    scalar := g[1,1];
    if scalar = zero then
        return false;
    fi;

    for i in [1..d] do
        for j in [1..d] do
            if (i = j) and g[i,j] <> scalar then
                return false;
            elif i <> j and g[i,j] <> zero then
                return false;
            fi;
        od;
    od;

    return true;

end;


# TODO: Implement next function
RECOG.MyIsAbsolutelyIrreducibleMatrixGroup := function(G)
local module;

    module := GModuleByMats(GeneratorsOfGroup(G), FieldOfMatrixGroup(G));
    return MTX.IsAbsolutelyIrreducible(module);

end;


# If g central in G, return true, else false

# Original input: (G :: GrpMat, g :: GrpMatElt) -> BoolElt
RECOG.IsCentral := function(G, g)
local gens, ele, one, invg;

    one := One(G);
    if g = one then 
        return true; 
    fi;
    if IsMatrixGroup(G) and IsFinite(FieldOfMatrixGroup(G)) and RECOG.MyIsAbsolutelyIrreducibleMatrixGroup(G) then
        return RECOG.IsScalarMatrix(g);
    fi;
    gens := GeneratorsOfGroup(G);
    invg := g^(-1);
    for ele in gens do
        if ele^(-1)*invg*ele*g <> one then
            return false;
        fi;
    od;
    return true;
end;


# TODO: Modify input such that it checks that G is an abelian group
# If g central in G, return true, else false

# Original input: (G :: GrpAb, g :: GrpAbElt) -> BoolElt
RECOG.IsCentralAb := function(G, g)
    return true;
end;


# TODO: Modify input such that it checks that G is a pc group
# If g central in G, return true, else false

# Original input: (G :: GrpPC, g :: GrpPCElt) -> BoolElt
RECOG.IsCentralPC := function(G, g)
local one, gens, ele, invg;

    one := One(G);
    if g = one then 
        return true; 
    fi;
    gens := GeneratorsOfGroup(G);
    invg := g^(-1);
    for ele in gens do
        if ele^(-1)*invg*ele*g <> one then
            return false;
        fi;
    od;
    return true;
end;


# TODO: Find GAP version for function MyPow

# Original input: (g: CGens := 0)
RECOG.MyPow := function(g, CGens)
    # L, T := Can(Matrix(g));
    # _, T, L := PrimaryRationalForm(Matrix(g));
    # TI := T^-1;
    # MA := Parent(T);
    # x := Parent(L[1, 1]).1;
    # P := Generic(Parent(g));

    # if CGens cmpne 0 then

    #     CGens := [T*X*TI: X in CGens];

    #     K := BaseRing(x);
    #     p := Characteristic(K);
    #     q := Size(K);

    #     return function(n)
    #         M := <>;
    #         pos := 1;
    #         BL := <>;
    #         posL := [];
    #         for t in L do

    #             # The following is equivalent to setting g to Modexp(x, n, f),
    #             # but is a bit more efficient (uses smaller exponent).

    #             f := t[1];
    #             d := Degree(f);
    #             m := q^d - 1;
    #             e := t[2];
    #             if e gt 1 then
    #                 beta := Ilog(p, e - 1) + 1;
    #                 m *:= p^beta;
    #                 f ^:= e;
    #                 d *:= e;
    #             fi;
    #             nm := n mod m;
    #             g := Modexp(x, nm, f);

    #             # assert g eq Modexp(x, n, f);

                
    #             # f := t[1]^t[2];
    #             # d := Degree(f);
    #             # g := Modexp(x, n, f);

    #             # f, g;

    #             B := [];
    #             for i := 0 to d - 1 do
    #                 B cat:= EltseqPad(g, d);
    #                 g := (g*x) mod f;
    #             od;

    #             B := Matrix(d, B);
    #             Append(~BL, B);
    #             Append(~posL, pos);
    #             pos +:= d;
    #         od;

    #         for X in CGens do
    #             LS := MA!0;
    #             RS := MA!0;

    #             for i := 1 to #BL do
    #                 pos := posL[i];
    #                 B := BL[i];
    #                 d := Ncols(B);
    #                 LB := B * RowSubmatrix(X, pos, d);
    #                 InsertBlock(~LS, LB, pos, 1);
    #                 RB := ColumnSubmatrix(X, pos, d) * B;
    #                 InsertBlock(~RS, RB, 1, pos);
    #                 delete LB, RB;
    #             od;

    #             if LS ne RS then
    #                 return false;
    #             fi;
    #         od;

    #         return true;
    #     ende function, L;

    # else

    #     return function(n)
    #         M := <>;
    #         pos := 1;
    #         S := MA!0;
    #         for t in L do
    #             f := t[1]^t[2];
    #             g := Modexp(x, n, f);
    #             # f, g;
    #             d := Degree(f);
    #             B := [];
    #             for i := 0 to d - 1 do
    #                 B cat:= EltseqPad(g, d);
    #                 g := (g*x) mod f;
    #             od;
    #             B := Matrix(d, B);
    #             B := B * RowSubmatrix(T, pos, d);
    #             InsertBlock(~S, B, pos, 1);
    #             delete B;
    #             pos +:= d;
    #         od;
    #         return P!(TI*S);
    #     ende function, L;

    # fi;
end;


# TODO: Write the next function

RECOG.FactoredOrder := function(g)

    return 0;

end;


# smallest n such that g^n is central in H 

# Original input: (H, g : Proof := true)
RECOG.MyCentralOrder := function (H, g, Proof)
local one, flag, o, USE_MyPow2, USE_MyPow, L , pow_ic, mp, fo, proof, primes, p, m, k, found, n, ic, j, h, pow;

    one := One(H);
    if g = one then 
        return [1, true]; 
    fi;

    if IsMatrixGroup(H) and IsFinite(FieldOfMatrixGroup(H)) and RECOG.MyIsAbsolutelyIrreducibleMatrixGroup(H) then
        # TODO: compare ProjectiveOrder functions
        #o := ProjectiveOrder(g, Proof);
        #flag := o[3];
        #o := o[1];
        o := RECOG.ProjectiveOrder(g);
        # TODO: add proof?
        flag := true;
        return [o, flag];
    fi;

    if RECOG.IsCentral(H, g) then 
        return [1, true]; 
    fi;

    USE_MyPow2 := false;
    USE_MyPow2 := true ; # and Ngens(H) le 2;

    USE_MyPow := false;
    USE_MyPow := true;

    # EOB addition
    
    if IsPerm(g) then
        USE_MyPow := false;
        USE_MyPow2 := false;
    fi;


    if USE_MyPow2 then
        pow_ic := RECOG.MyPow(g, GeneratorsOfGroup(H));
        L := pow_ic[2];
        pow_ic := pow_ic[1];

        mp := Lcm(List(L,t -> t[1]^t[2]));
        #assert mp eq MinimalPolynomial(g);
        fo := RECOG.FactoredOrder(mp, Proof);
        #assert fo eq FactoredOrder(g);
        if Size(fo) = 1 and fo[1, 2] = 1 then 
            return [fo[1, 1], Proof]; 
        fi;
        proof := Proof;
    else
        if IsMatrixGroup(H) and IsFinite (FieldOfMatrixGroup(H))  then 
            fo := RECOG.FactoredOrder(g, Proof);
            proof := fo[2];
            fo := fo[1];
        else
            # EOB addition
            if IsPerm(g) then 
                o := Order(g); 
                fo := Collected(Factors(o));
            else 
                fo := RECOG.FactoredOrder(g);
            fi;
            proof := true;
        fi;

        # if IsPrime (o) then return o, proof; end if;
        if Size(fo) = 1 and fo[1, 2] = 1 then 
            return [fo[1, 1], proof]; 
        fi;

        if USE_MyPow then
            pow := RECOG.MyPow(g);
        fi;
    fi;

    # primes := Factorisation (o);
    primes := fo;
    o := RECOG.FactorizationToInteger(fo);

    for j in [1..Size(primes)] do
        p := primes[j][1];
        m := primes[j][2];
        k := 0;
        found := false;
        repeat
            n := o/p;

            if USE_MyPow2 then
                ic := pow_ic(n);
            else
                if USE_MyPow then
                    h := pow(n);
                else
                    h := g^n;
                fi;
                ic := RECOG.IsCentral(H, h);
            fi;

            if ic then
                o := n;
            else
                found := true;
            fi;

            k := k + 1;
        until found or (k = m);
    od;

    return [o, proof];
end;


# return smallest n such that g^n is central in its parent,
# which can be supplied as the optional argument ParentGroup.
# If Proof is false then accept a multiple of this value;
# the second value returned is true if the answer is exact.

# Original input: (g:: GrpMatElt: ParentGroup := Parent (g), Proof := true) -> RngIntElt, BoolElt
RECOG.CentralOrder := function (g, ParentGroup, Proof)

    return RECOG.MyCentralOrder(ParentGroup, g, Proof);

end;


# Original input: (g:: GrpMatElt: ParentGroup := Parent (g), Proof := true) -> RngIntElt, BoolElt
RECOG.CentralOrder := function (g)

    return RECOG.ProjectiveOrder(g);

end;


# Original input: G, order: Randomiser := Internal_RandomProcess(G : WordGroup := WordGroup(G)),  MaxTries := 100, Central := false, Proof := true
RECOG.MyRandomElementOfOrder := function (G, order, Randomiser,  MaxTries, Central, Proof) 
local g, q, r, w, i, fct, o, precise;

    if Central then 
        fct := RECOG.CentralOrder; 
    else 
        fct := Order; 
    fi;

    i := 0;
    repeat
        g := Random(Randomiser);
        w := g[2];
        g := g[1];

        # compute order 
        if IsMatrix(g) then     
            o := fct(g, Proof);
            precise := o[2];
            o := o[1];
            q := QuoInt(o, order);
            r := o mod order;
            #q, r := Quotrem(o, order);
        else 
            o := fct(g);
            q := QuoInt(o, order);
            r := o mod order;
            # q, r := Quotrem(fct(g), order);
            precise := true;
        fi;
        i := i + 1;
    until (r = 0) or (i >= MaxTries and MaxTries > 0);

    if r <> 0 then
        Print("UserUtil, 1: Element of order", order, "not found in", MaxTries, "attempts");
        return [false, fail, fail, fail];
    fi;

    return [true, g^q, w^q, precise];
end;


# Original input: G, order : Randomiser := Internal_RandomProcess(G : WordGroup := WordGroup(G)),  MaxTries := 100
RECOG.MyRandomElementOfPrimeOrder := function(G, order, Randomiser, MaxTries) 
local i, g, w, n, flag;

    i := 0;
    repeat
        g := Random(Randomiser);
        w := g[2];
        g := g[1];

        n := RECOG.PrimeOrderElement(g, order);
        flag := n[2];
        n := n[1];
        i := i + 1;
    until flag or (i >= MaxTries and MaxTries > 0);

    if not(flag) then
        Print("UserUtil, 1: Element of order", order, "not found in", MaxTries, "attempts");
        return [false, fail, fail];
    fi;

    return [true, g^n, w^n];
end;


# Search for a random element of specified prime order.
#    If such is found, then return true, the element, and its SLP.
#    MaxTries is the maximum number of random elements that are chosen. 
#    Randomiser is the random process used to construct these,
#    and the SLP for the returned element is in the word group of 
#    this process. 

# Original input: (G :: GrpMat, order :: RngIntElt : Randomiser := Internal_RandomProcess(G : WordGroup := WordGroup(G)), MaxTries := 100) -> BoolElt, GrpMatElt, GrpSLPElt
RECOG.RandomElementOfPrimeOrder := function(G, order, Randomiser, MaxTries)

    return RECOG.MyRandomElementOfPrimeOrder(G, order, Randomiser, MaxTries); 

end;


# Search for a random element of specified order.
#      If such is found, then return true, the element, and its SLP.
#      If Proof is false, then accept
#      an element whose order may be a multiple of the desired order.
#      The final value returned indicates whether
#      the element is known to have the precise order. 
#      If Central then search for an element which has this order 
#      modulo the centre of G.
#      MaxTries is the maximum number of random elements that are chosen. 
#      Randomiser is the random process used to construct these,
#      and the SLP for the returned element is in the word group of 
#      this process. 

# Original input: (G :: GrpMat, order :: RngIntElt : Randomiser := Internal_RandomProcess(G : WordGroup := WordGroup(G)), MaxTries := 100, Central := false, Proof := true) -> BoolElt, GrpMatElt, GrpSLPElt, BoolElt
RECOG.RandomElementOfOrder := function(G, order, Randomiser, MaxTries, Central, Proof)
    
    return RECOG.MyRandomElementOfOrder(G, order, Central, Randomiser, MaxTries, Proof); 

end;


# multiplicative upper bound for order of x

RECOG.MultiplicativeUpperbound := function (x)
local F, p, q, m, facs, degs, alpha, beta, bound;

    x := StripMemory(x);
    F := FieldOfMatrixList([x]);
    p := Characteristic(F);
    q := Size(F);
    m := MinimalPolynomial(x);
    facs := Collected(Factors(m));
    degs := List([1..Size(facs)], i -> Degree(facs[i][1]));
    alpha := Maximum(List([1..Size(facs)], i -> facs[i][2]));
    beta := Log(alpha,p);
    if not(p^alpha = beta) then
        beta := beta + 1;
    fi;
    bound := Lcm(List(degs,i-> q^i - 1)) * p^beta;
    return bound;
end;

# obtain an upper bound for the order of x as 2^k * odd,
#   where the power k of 2 in the factorisation is correct; 
#   c^(o * bound) is the identity, o = 2^k and y = c^bound 
#   bound is odd 

# Aka PseudoOrder algorithm
RECOG.EstimateOrder := function (x)
local bound, k, y, o;

    bound := RECOG.MultiplicativeUpperbound(x);

    # largest odd divisor of upper bound 
    k := 0; 
    while (bound mod 2) = 0 do 
        k := k + 1; 
        bound := bound/2; 
    od;

    # obtain element of even order by powering up odd part 
    if k > 0 then 
        y := x^bound; 
    else 
        y := x^0; 
    fi;
    o := Order(y);
    return [bound * o, y, o, bound];
end;


# can we obtain an involution which is a power of x? 
#   if degree and field is large, then powering up odd 
#   part of x and computing order of resulting 2-power element 
#   is faster than computing the order of x */

# Original input: (x: w := [])
RECOG.InvolutionIsPower := function (x, w)
local bound, y, o;
    # "method 1";

    bound := RECOG.MultiplicativeUpperbound(x);
    # largest odd divisor of upper bound */
    while (bound mod 2) = 0 do 
        bound := bound/2; 
    od;

    # obtain element of even order by powering up odd part 
    y := x^bound;
    o := Order (y);
    if (o mod 2) = 0 then
        y := y^(o/2);
        if not(w = []) then 
            w := w^bound; 
            w := w^(o/2); 
            return [true, y, w];
        fi;
        return [true, y, fail];
    else
        return [false, fail, fail];
    fi;
end;


# Original input: y: w := []
RECOG.OrderToInvolution := function (y, w)
local o;
    # "method 2";
    # Order (y, Proof := false);
    o := Order(y, false);
    if (o mod 2) = 0 then
        o := o /2;
        y := y^(o);
        if not(w = []) then 
            w := w^(o); 
            return [true, y, w];
        fi;
        return [true, y, fail];
    else
        return [false, fail, fail];
    fi;
end;



# Original input: (G: Words := true)
RECOG.GenerateInvolution := function (G, Words)
local x, w, F, p, e, d;
   
    if Words then 
        # TODO: Add version with word
        x := PseudoRandom(G);
        w := x[2];
        x := x[1];
    else 
        x := PseudoRandom(G);
        w := [];
    fi;

    F := FieldOfMatrixGroup(G);
    p := Characteristic(F);
    e := Size(Factors(Size((F))));
    d := Degree(G);

    if   d >= 20 and p >= 5 and e >= 1 then 
        return RECOG.InvolutionIsPower(x, w);
    elif d >= 13 and p >= 11 and e >= 2 then 
        return RECOG.InvolutionIsPower(x, w);
    elif d >=  9 and p >= 11 and e >= 4 then 
        return RECOG.InvolutionIsPower(x, w);
    elif d >=  5 and p >= 11 and e >= 4 then 
        return RECOG.InvolutionIsPower(x, w);
    elif d =  4 and p >= 11 and e >= 7 then 
        return RECOG.InvolutionIsPower(x, w);
    elif d =  3 and p >= 11 and e >= 9 then 
        return RECOG.InvolutionIsPower(x, w);
    elif d >=  4 and p =  7 and e >= 8 then 
        return RECOG.InvolutionIsPower(x, w);
    elif d >=  4 and p =  5 and e >= 8 then 
        return RECOG.InvolutionIsPower(x, w);
    elif d >=  4 and p =  3 and e >= 10 then 
        return RECOG.InvolutionIsPower(x, w);
    else 
        return RECOG.OrderToInvolution(x, w); 
    fi;
end;

# Fct can be Order or ProjectiveOrder; search at most Limit times for 
#  element of (projective) order RequiredOrder; if found return element
#  and possibly word, else return false

# Original input: (G :: Grp, RequiredOrder, Limit:: RngIntElt: Word := true, Fct := Order) -> GrpMatElt
RECOG.ElementOfOrder := function(G, RequiredOrder, Limit, Word, Fct)
local NmrTries, o, exists, g, wg, rem, x;

    if IsMatrixGroup(G) then 
        Fct := Order; 
    fi;

    if IsInt(RequiredOrder) then
        RequiredOrder := Set([RequiredOrder]);
    fi;

    NmrTries := Limit;
    rem := false;
    repeat
        if Word then
            # TODO: Add word version here 
            g := PseudoRandom(G);
            wg := g[2];
            g := g[1];
            if IsBool(g) then 
                return [false, fail]; 
            fi;
        else 
            g := PseudoRandom(G);
        fi;
        o := Fct(g);
        NmrTries := NmrTries - 1;
        for exists in RequiredOrder do
            if (o mod exists) = 0 then
                rem := true;
            fi;
        od;
    until rem or (NmrTries = 0);

    if rem then 
        o := o/x; 
        if Word then 
            return [g^o, wg^o]; 
        else 
            return [g^o, fail]; 
        fi; 
    fi;

    return [false, fail];

end;


# p is a prime. Determine if p divides the order of g and if so 
#      return true, an element h of order a power of p, a 
#      multiplicative upper bound for order of h, 
#      the power of g equal to h, and a flag indicating if the upper bound
#      is the true order. 

# Original input: (g :: GrpElt, p :: RngIntElt :Proof := false) -> BoolElt, GrpElt, RngIntElt, RngIntElt, BoolElt
RECOG.PrimePowerOrderElement := function(g, p, Proof)
local k, s, b, n, precise;

    if not IsPrime(p) then
        Error("p must be a prime number");
    fi;

    # Avoid integer factorisation if Proof is false,
    # obtain multiplicative upper bound
    if IsMatrix(g) then 
        # TODO: Add proof version
        n := Order(g, Proof);
        precise := n[2];
        n := n[1];
    else 
        n := Order(g);
        precise := true; 
    fi;

    # TODO: compare next function
    k := Valuation(n, p);
    s := k[2];
    k := k[1];
    b := g^s;
    return [b <> g^0, b, p^k, s, precise];
end;


# p is a prime. Determine if p divides the order of g and if so return true
#    and the power of g which gives an element of order p.
#
#    The algorithm is Las Vegas polynomial time, in particular it avoids
#    integer factorisation. 

# Original input: (g :: GrpElt, p :: RngIntElt) -> BoolElt, RngIntElt
RECOG.PrimeOrderElement := function(g, p)
local flag, b, n, s, precise, r, bounds, i, k;
    
    flag := RECOG.PrimePowerOrderElement(g, p);
    b := flag[2];
    n := flag[3];
    s := flag[4];
    precise := flag[5];
    flag := flag[1];

    if flag then
        if precise then
            r := n/p;
            flag := IsInt(r);
            Assert(flag, true);

            return [true, s * r];
        else
            # TODO: Add next function
            k := Valuation(n, p);

            # Binary search for the correct power
            bounds := [1, k];
            while bounds[2] > bounds[1] do
                i := Floor(Sum(bounds)/2);

                if (b^(p^i) = g^0) then
                    bounds[2] := i;
                else
                    bounds[1] := i + 1;
                fi;
            od;

            return [true, s * (p^(bounds[1] - 1))];
        fi;
    else
        return [false, fail];
    fi;
end;


# Original input: (G : Randomiser := Internal_RandomProcess(G : WordGroup := WordGroup(G)), MaxTries := 1000) 
RECOG.RandomInvolution := function (G, Randomiser, MaxTries) 
local flag, g, slp;

    repeat
	    flag := RECOG.RandomElementOfPrimeOrder(G, 2, Randomiser, MaxTries);
        g := flag[2]; 
        slp := flag[3];
        flag := flag[1];
    until flag;

    return [g, slp];
end;

# G \leq GL(d, q). Determines if (P)SL(d, q) is contained in G. The
# algorithm is one-sided Monte Carlo and a positive answer is always
# correct. The error probability is at most ErrorProb.
#
# Randomiser is used to find random elements of G. If Projective is true then
# PSL rather than SL is used. 

# Original input: (G : Randomiser := Internal_RandomProcess(G), ErrorProb := 2^(-100), Projective := false, q := Size(CoefficientRing(G))) 
RECOG.IsProbablySL2 := function(G, Randomiser, ErrorProb, Projective, q) 
local foundFirst, foundSecond, order, i, prob, nrElements, fct, goodOrder1, goodOrder2;

    foundFirst := false;
    foundSecond := false;
    i := 0;

    # EOB -- added next line since SL(2, q) = PSL(2, q) when q is even 
    if (q mod 2) = 0 then 
        Projective := false; 
    fi;

    # A crude estimate of the error probability is used
    nrElements := Int(Log(ErrorProb) / Log((1 - Phi(q - 1) / (q - 1)) * (1 - Phi(q + 1) / (q + 1)))) + 1;

    nrElements := Maximum([nrElements, 100]);    
    Print("UserUtil, 2: Checking ", nrElements, " elements\n");

    if IsMatrixGroup(G) then
        # fct := func<g | Order(g : Proof := false)>;
        fct := function(g)
            return Order(g, false);
        end;
    else
        fct := function(g)
            return Order(g);
        end;
    fi;

    if Projective then
        goodOrder1 := (q - 1)/2;
        goodOrder2 := (q + 1)/2;
    else
        goodOrder1 := q-1;
        goodOrder2 := q+1;
    fi;

    # If we can find elements of order (q ± 1) / 2 then we have PSL(2, q)
    repeat
        order := fct(Random(Randomiser));

        if order = goodOrder1 then
            foundFirst := true;
        elif order = goodOrder2 then
            foundSecond := true;
        fi;

        i := i + 1;
    until i >= nrElements or (foundSecond and foundFirst);

    return (foundFirst and foundSecond);
end;


###################################################################################################
###################################################################################################
######## Bray algorithm ###########################################################################
###################################################################################################
###################################################################################################

# Translated from Magma by DR

# Original input: G, g, wg: Central := false, Proof := false, NumberRandom := 100, SLPs := [], 
#                 CompletionCheck := func<G, C, g, l | NumberOfGenerators(C) ge 20>, 
#                 Randomiser := Internal_RandomProcess(G : WordGroup := WordGroup(G))

# TODO: Add SLP version
RECOG.MyCentraliserOfInvolution := function(G, g, wg, Central, Proof, NumberRandom, SLPs, CompletionCheck, Randomiser)
local centraliser, element, commutator, q, r, residue, slpMap, word, nGens, fct, R, testset, testgroup, mat, o;

    if Central then 
        fct := RECOG.CentralOrder; 
    else 
        fct := Order; 
    fi;

    R := Randomiser;

    centraliser := [g];
    nGens := 1;
    slpMap := [wg];

    Info(InfoRecog,3,"Centraliser, 1: Starting Bray algorithm \n");
    repeat
        NumberRandom := NumberRandom - 1;
        element := R(G);
        commutator := g^(-1)*element^(-1)*g*element;
        # compute order 
        o := fct(commutator);
        r := o mod 2;
        q := Int(o/2);

        if r = 1 then

            Info(InfoRecog,3,"Centraliser, 2: Odd case \n");
            mat := element * commutator^q;
            testset := MutableCopyMat(centraliser);
            Add(testset, mat);
            testgroup := GroupByGenerators(testset);
            if Size(SmallGeneratingSet(testgroup)) > nGens then
                Add(centraliser, mat);
                nGens := nGens + 1;
            fi;

        else
            Info(InfoRecog,3,"Centraliser, 2: Even case \n");
            mat := commutator^q;
            testset := MutableCopyMat(centraliser);
            Add(testset, mat);
            testgroup := GroupByGenerators(testset);
            if Size(SmallGeneratingSet(testgroup)) > nGens then
                Add(centraliser, mat);
                nGens := nGens + 1;
            fi;

            mat := (g^(-1) * element * g * element^(-1))^q;
            testset := MutableCopyMat(centraliser);
            Add(testset, mat);
            testgroup := GroupByGenerators(testset);
            if Size(SmallGeneratingSet(testgroup)) > nGens then
                Add(centraliser, mat);
                nGens := nGens + 1;
            fi;
        fi;

        Info(InfoRecog,3,"Centraliser, 2: Check centraliser completion \n");
    until CompletionCheck(G, centraliser, g, slpMap) or (NumberRandom = 0);

    Info(InfoRecog,3,"Centraliser, 1: Bray algorithm finished \n");

    return [centraliser,slpMap];
end;


RECOG.CompletionCheck := function(G,centraliser, g, slp)

	if Size(centraliser) >= 20 then
	return true;
	else
	return false;
	fi;
	
end;


RECOG.MyCentraliserOfInvolutionVersion2 := function(G, g, wg, Central, Proof, NumberRandom, SLPs, CompletionCheck, Randomiser)
local centraliser, element, commutator, q, r, residue, slpMap, word, nGens, fct, R, testset, testgroup, mat, o;

    if Central then 
        fct := RECOG.CentralOrder; 
    else 
        fct := Order; 
    fi;

    R := Randomiser;

    centraliser := [g];
    nGens := 1;
    slpMap := [wg];

    Info(InfoRecog,3,"Centraliser, 1: Starting Bray algorithm \n");
    repeat
        NumberRandom := NumberRandom - 1;
        element := R(G);
        commutator := g^(-1)*element^(-1)*g*element;
        # compute order 
        o := fct(commutator);
        r := o mod 2;
        q := Int(o/2);

        if r = 1 then

            Info(InfoRecog,3,"Centraliser, 2: Odd case \n");
            mat := element * commutator^q;
            if not(mat in centraliser) then
                Add(centraliser, mat);
                nGens := nGens + 1;
            fi;

        else
            Info(InfoRecog,3,"Centraliser, 2: Even case \n");
            mat := commutator^q;
            if not(mat in centraliser) then
                Add(centraliser, mat);
                nGens := nGens + 1;
            fi;

            mat := (g^(-1) * element * g * element^(-1))^q;
            if not(mat in centraliser) then
                Add(centraliser, mat);
                nGens := nGens + 1;
            fi;
        fi;

        Info(InfoRecog,3,"Centraliser, 2: Check centraliser completion \n");
    until CompletionCheck(G, centraliser, g, slpMap) or (NumberRandom = 0);

    Info(InfoRecog,3,"Centraliser, 1: Bray algorithm finished \n");

    return [centraliser,slpMap];
end;


RECOG.FindSwappingElement := function(G, g, wg, NumberRandom, SLPs, Randomiser)
local centraliser, element, commutator, q, r, residue, slpMap, word, nGens, fct, R, testset, testgroup, mat, o;

    fct := RECOG.CentralOrder; 

    R := Randomiser;

    centraliser := [g];
    nGens := 1;
    slpMap := [wg];

    Info(InfoRecog,3,"Centraliser, 1: Starting Bray algorithm \n");
    repeat
        NumberRandom := NumberRandom - 1;
        element := R(G);
        commutator := g^(-1)*element^(-1)*g*element;
        # compute order 
        o := fct(commutator);
        r := o mod 2;
        q := Int(o/2);

        if r = 1 then

            Info(InfoRecog,3,"Centraliser, 2: Odd case \n");
            mat := element * commutator^q;
            if mat^(-1)*g*mat <> g then
                return g;
            fi;

            if not(mat in centraliser) then
                Add(centraliser, mat);
                nGens := nGens + 1;
            fi;

        else
            Info(InfoRecog,3,"Centraliser, 2: Even case \n");
            mat := commutator^q;
            if mat^(-1)*g*mat <> g then
                return g;
            fi;
            if not(mat in centraliser) then
                Add(centraliser, mat);
                nGens := nGens + 1;
            fi;

            if mat^(-1)*g*mat <> g then
                return g;
            fi;
            mat := (g^(-1) * element * g * element^(-1))^q;
            if not(mat in centraliser) then
                Add(centraliser, mat);
                nGens := nGens + 1;
            fi;
        fi;

        Info(InfoRecog,3,"Centraliser, 2: Check centraliser completion \n");
    until (NumberRandom = 0);

    Info(InfoRecog,3,"Centraliser, 1: Bray algorithm finished \n");

    return fail;
end;


# TODO: We need MultiplicativeUpperbound for Projective group elements
RECOG.FindSwappingElementVersion2 := function(G, g, wg, NumberRandom, SLPs, Randomiser)
local centraliser, element, commutator, q, r, residue, slpMap, word, nGens, fct, R, testset, testgroup, mat, o;

    fct := RECOG.CentralOrder; 

    R := Randomiser;

    centraliser := [g];
    nGens := 1;
    slpMap := [wg];

    Info(InfoRecog,2,"Centraliser, 1: Starting Bray algorithm \n");
    repeat
        NumberRandom := NumberRandom - 1;
        element := R(G);
        commutator := g^(-1)*element^(-1)*g*element;
        # compute order 

        o := RECOG.MultiplicativeUpperbound(commutator);
        if o mod 2 = 0 then
            r := 0;
        else
            r := 1;
        fi;

        if r = 1 then

            o := fct(commutator);
            r := o mod 2;
            q := Int(o/2);

            Info(InfoRecog,2,"Centraliser, 2: Odd case \n");
            mat := element * commutator^q;
            if mat^(-1)*g*mat <> g then
                return g;
            fi;

            if not(mat in centraliser) then
                Add(centraliser, mat);
                nGens := nGens + 1;
            fi;

        else
            Info(InfoRecog,2,"Element not good");
        fi;

        Info(InfoRecog,2,"Centraliser, 2: Check centraliser completion \n");
    until (NumberRandom = 0);

    Info(InfoRecog,2,"Centraliser, 1: Bray algorithm finished \n");

    return fail;
end;


#    g is an involution in G, and wg is an SLP for g. 
#    Return the centraliser C of g in G, and SLPs of the generators of C.
#    Randomiser is the random process used to construct the 
#    elements and the SLP for g must lie in the word group of this process. 
#
#    The algorithm used is that of John Bray.  Since it is Monte Carlo, 
#    it may return only a subgroup of the centraliser. 
#
#    If Central then construct the projective centraliser of  g.
#    The function CompletionCheck is used to determine when we have 
#    constructed the centraliser.  It takes arguments G, C, g 
#    and SLPs for generators of C as input, and 
#    returns true or false.  By default, the algorithm completes when the 
#    centraliser has 20 generators or considered NumberRandom elements.

# Original input:  G :: GrpMat, g :: GrpMatElt, wg :: GrpSLPElt : Central := false, NumberRandom := 100, 
#                  CompletionCheck := func<G, C, g, l | NumberOfGenerators(C) ge 20>, 
#                  Randomiser := Internal_RandomProcess(G : WordGroup := WordGroup(G)) 
# Original output: GrpMat, SeqEnum
RECOG.CentraliserOfInvolution := function(G, g, wg, Central, NumberRandom, CompletionCheck, Randomiser)
local fct;
    
    if Central then 
        fct := RECOG.ProjectiveOrder; 
    else 
        fct := Order; 
    fi;

    if not(fct(g) = 2) then
        Error("Centraliser of involution: <g> must be an involution");
    fi;

    return RECOG.MyCentraliserOfInvolutionVersion2(G, g, wg, Central, false, NumberRandom, [], CompletionCheck, Randomiser);
end;


###################################################################################################
###################################################################################################
######## Black box algorithms #####################################################################
###################################################################################################
###################################################################################################

RECOG.BlaxBoxGoingDownStepVersion0_SL := function( grp, d, q )
local e, eprime, B, r, ppdlist, goode, i, j, ppds, f, p, factors, counter, l, one, foundFirst, foundSecond, g, g2, ppds2, min, max;

    # Start by preparing a list of good e and corresponding ppds
    factors := Factors(q);
    f := Size(factors);
    p := factors[1];
    one := One(grp);
    foundFirst := false;
    ppdlist := [];
    #goode := Log2Int(d);  ##Do we need this?

    min := 2;
    max := Minimum([Log2Int(d), Int(d/2 - 1)]);
    
    # New test for making B smaller
    for e in [min..max] do
    #for e in [Maximum([2,Log2Int(d)])..Minimum([5*Log2Int(d), Int(d/2 - 1)])] do
        eprime := d - e;
        # Factors is bad since the numbers get too large. We need something else to find the ppds
        ppds := Factors(PrimitivePrimeDivisors(f*e,p).ppds);
        ##### Change 
        #ppds2 := Factors(PrimitivePrimeDivisors(f*eprime,p).ppds);
        #Add(ppdlist,[e,eprime,ppds,ppds2]);
        Add(ppdlist,[e,eprime,ppds]);
        #####
    od;

    counter := 1;
    while counter < 1000 do
        g := PseudoRandom(grp);
        B := 1;
        if (g <> one) then
            for l in ppdlist do
                B := (q^(l[1])-1)*(q^(l[2])-1);
                # This version works
                #if (g^(B/(l[3,1])) <> one) and (g^(B/(l[4,1])) <> one) and (g^B = one) then
                #    break;
                #fi;
                if (g^B = one) then
                    break;
                fi;
            od;
        fi;

        if (g^B = one) then
            ppds := l[3];
            for i in ppds do
                if (i > 1) and ((q^(l[2])-1) mod i <> 0) then
                    for j in [1..d] do
                        if (B mod (i^j) = 0) and (g^(B/i^j) <> one) then
                            #Error("here");
                            foundFirst := true;
                            g := g^(B/i^j);
                            break;
                        fi; 
                    od;
                fi;
                if foundFirst then
                    break;
                fi;
            od;
        fi;
        counter := counter + 1;
        if foundFirst then
            break;
        fi;
    od;

    foundSecond := false;
    if foundFirst then
        counter := 1;
        while counter < 1000 do
            g2 := PseudoRandom(grp);
            B := 1;
            if (g2 <> one) then
                for l in ppdlist do
                    B := (q^(l[1])-1)*(q^(l[2])-1);
                    # This version works
                    #if (g2^(B/(l[3,1])) <> one) and (g2^(B/(l[4,1])) <> one) and (g2^B = one) then
                    #    break;
                    #fi;
                    if (g2^B = one) then
                        break;
                    fi;
                od;
            fi;

            if (g2^B = one) then
                ppds := l[3];
                for i in ppds do
                    if (i > 1) and ((q^(l[2])-1) mod i <> 0) then
                        for j in [1..d] do
                            if (B mod (i^j) = 0) and (g2^(B/i^j) <> one) then
                                foundSecond := true;
                                g2 := g2^(B/i^j);
                                break;
                            fi; 
                        od;
                    fi;
                    if foundSecond then
                        break;
                    fi;
                od;
            fi;
            counter := counter + 1;
            if foundSecond then
                break;
            fi;
        od;
    fi;

    if foundFirst and foundSecond then
        return [g,g2];
    fi;

    return fail;
end;


RECOG.BlaxBoxGoingDownStepVersion1_SL := function( grp, d, q )
local e, eprime, B, r, ppdlist, goode, i, j, ppds, f, p, factors, counter, l, one, foundFirst, foundSecond, g, g2, ppds2, min, max, firstok, secondok;

    # Start by preparing a list of good e and corresponding ppds
    factors := Factors(q);
    f := Size(factors);
    p := factors[1];
    one := One(grp);
    foundFirst := false;
    ppdlist := [];
    #goode := Log2Int(d);  ##Do we need this?

    if d <= 20 then
        min := 2;
        # 2*Log2Int(d)?
        max := Minimum([Log2Int(d), Int(d/2 - 1)]);
    else
        min := Log2Int(d);
        max := Minimum([5*Log2Int(d), Int(d/2 - 1)]);
    fi;
    
    # New test for making B smaller
    for e in [min..max] do
    #for e in [Maximum([2,Log2Int(d)])..Minimum([5*Log2Int(d), Int(d/2 - 1)])] do
        eprime := d - e;
        # Factors is bad since the numbers get too large. We need something else to find the ppds
        ppds := Factors(PrimitivePrimeDivisors(f*e,p).ppds);
        ##### Change 
        #ppds2 := Factors(PrimitivePrimeDivisors(f*eprime,p).ppds);
        #Add(ppdlist,[e,eprime,ppds,ppds2]);
        Add(ppdlist,[e,eprime,ppds]);
        #####
    od;

    counter := 1;
    while counter < 1000 do
        g := PseudoRandom(grp);
        firstok := false;
        if (g <> one) then
            for l in ppdlist do
                B := (q^(l[1])-1)*(q^(l[2])-1);
                # This version works
                #if (g^(B/(l[3,1])) <> one) and (g^(B/(l[4,1])) <> one) and (g^B = one) then
                #    break;
                #fi;
                if (g^B = one) then
                    firstok := true;
                    break;
                fi;
            od;
        fi;

        if firstok then
            ppds := l[3];
            for i in ppds do
                if (i > 1) and ((q^(l[2])-1) mod i <> 0) then
                    #### B' := B/(i^j_max);
                    # B' := B/ppds;
                    # h := g^B';
                    # if g <> one then
                        # foundFirst := true;
                        # g := h;
                    #fi;
                    for j in [1..d] do
                        if (B mod (i^j) = 0) and (g^(B/i^j) <> one) then
                            #Error("here");
                            foundFirst := true;
                            g := g^(B/i^j);
                            break;
                        fi; 
                    od;
                fi;
                if foundFirst then
                    break;
                fi;
            od;
        fi;
        counter := counter + 1;
        if foundFirst then
            break;
        fi;
    od;

    foundSecond := false;
    if foundFirst then
        counter := 1;
        secondok := false;
        while counter < 1000 do
            g2 := PseudoRandom(grp);
            if (g2 <> one) then
                for l in ppdlist do
                    B := (q^(l[1])-1)*(q^(l[2])-1);
                    # This version works
                    #if (g2^(B/(l[3,1])) <> one) and (g2^(B/(l[4,1])) <> one) and (g2^B = one) then
                    #    break;
                    #fi;
                    if (g2^B = one) then
                        secondok := true;
                        break;
                    fi;
                od;
            fi;

            if secondok then
                ppds := l[3];
                for i in ppds do
                    if (i > 1) and ((q^(l[2])-1) mod i <> 0) then
                        for j in [1..d] do
                            if (B mod (i^j) = 0) and (g2^(B/i^j) <> one) then
                                foundSecond := true;
                                g2 := g2^(B/i^j);
                                break;
                            fi; 
                        od;
                    fi;
                    if foundSecond then
                        break;
                    fi;
                od;
            fi;
            counter := counter + 1;
            if foundSecond then
                break;
            fi;
        od;
    fi;

    if foundFirst and foundSecond then
        return [g,g2];
    fi;

    return fail;
end;


RECOG.BlaxBoxGoingDownStepVersion2_SL := function( grp, d, q )
local e, eprime, B, r, ppdlist, goode, i, j, ppds, f, p, factors, counter, l, one, foundFirst, foundSecond, g, g2, ppds2, min, max, firstok, secondok, B2, h, NFactors;

    # Start by preparing a list of good e and corresponding ppds
    factors := Factors(q);
    f := Size(factors);
    p := factors[1];
    one := One(grp);
    foundFirst := false;
    ppdlist := [];
    #goode := Log2Int(d);  ##Do we need this?

    if d <= 20 then
        min := 2;
        # 2*Log2Int(d)?
        max := Minimum([Log2Int(d), Int(d/2 - 1)]);
    else
        min := Log2Int(d);
        max := Minimum([5*Log2Int(d), Int(d/2 - 1)]);
    fi;
    
    # New test for making B smaller
    for e in [min..max] do
    #for e in [Maximum([2,Log2Int(d)])..Minimum([5*Log2Int(d), Int(d/2 - 1)])] do
        eprime := d - e;
        # Factors is bad since the numbers get too large. We need something else to find the ppds
        ppds := PrimitivePrimeDivisors(f*e,p).ppds;
        ppds := ppds/Gcd(ppds,(q^eprime-1));
        NFactors := PrimeDivisors(ppds);
        ppds := Product(NFactors);
        ##### Change 
        #ppds2 := Factors(PrimitivePrimeDivisors(f*eprime,p).ppds);
        #Add(ppdlist,[e,eprime,ppds,ppds2]);
        Add(ppdlist,[e,eprime,ppds]);
        #####
    od;

    counter := 1;
    while counter < 1000 do
        g := PseudoRandom(grp);
        firstok := false;
        if (g <> one) then
            for l in ppdlist do
                B := (q^(l[1])-1)*(q^(l[2])-1);
                # This version works
                #if (g^(B/(l[3,1])) <> one) and (g^(B/(l[4,1])) <> one) and (g^B = one) then
                #    break;
                #fi;
                if (g^B = one) then
                    firstok := true;
                    break;
                fi;
            od;
        fi;

        if firstok then
            ppds := l[3];
            B2 := B/ppds;
            # if ggt((q^e'-1),ppds) = 1 then
            # dont continue
            h := g^B2;
            if h <> one then
                foundFirst := true;
                g := h;
            fi;
        fi;
        counter := counter + 1;
        if foundFirst then
            break;
        fi;
    od;

    foundSecond := false;
    if foundFirst then
        counter := 1;
        secondok := false;
        while counter < 1000 do
            g2 := PseudoRandom(grp);
            if (g2 <> one) then
                for l in ppdlist do
                    B := (q^(l[1])-1)*(q^(l[2])-1);
                    # This version works
                    #if (g2^(B/(l[3,1])) <> one) and (g2^(B/(l[4,1])) <> one) and (g2^B = one) then
                    #    break;
                    #fi;
                    if (g2^B = one) then
                        secondok := true;
                        break;
                    fi;
                od;
            fi;

            if secondok then
                ppds := l[3];
                # if ggt((q^e'-1),ppds) = 1 then
                # dont continue
                B2 := B/ppds;
                h := g2^B2;
                if h <> one then
                    foundSecond := true;
                    g2 := h;
                fi;
            fi;
            counter := counter + 1;
            if foundSecond then
                break;
            fi;
        od;
    fi;

    if foundFirst and foundSecond then
        return [g,g2];
    fi;

    return fail;
end;


RECOG.BlaxBoxGoingDownStepVersion3_SL := function( grp, d, q )
local e, eprime, B, r, ppdlist, goode, i, j, ppds, f, p, factors, counter, l, one, foundFirst, foundSecond, g, g2, ppds2, min, max;

    # Start by preparing a list of good e and corresponding ppds
    factors := Factors(q);
    f := Size(factors);
    p := factors[1];
    one := One(grp);
    foundFirst := false;
    ppdlist := [];
    #goode := Log2Int(d);  ##Do we need this?

    if d <= 20 then
        min := 2;
        # 2*Log2Int(d)?
        max := Minimum([Log2Int(d), Int(d/2 - 1)]);
    else
        min := Log2Int(d);
        max := Minimum([5*Log2Int(d), Int(d/2 - 1)]);
    fi;
    
    # New test for making B smaller
    for e in [min..max] do
    #for e in [Maximum([2,Log2Int(d)])..Minimum([5*Log2Int(d), Int(d/2 - 1)])] do
        eprime := d - e;
        # Factors is bad since the numbers get too large. We need something else to find the ppds
        ppds := Factors(PrimitivePrimeDivisors(f*e,p).ppds);
        ##### Change 
        #ppds2 := Factors(PrimitivePrimeDivisors(f*eprime,p).ppds);
        #Add(ppdlist,[e,eprime,ppds,ppds2]);
        Add(ppdlist,[e,eprime,ppds]);
        #####
    od;

    counter := 1;
    while counter < 1000 do
        g := PseudoRandom(grp);
        B := 1;
        if (g <> one) then
            for l in ppdlist do
                B := (q^(l[1])-1)*(q^(l[2])-1);
                # This version works
                #if (g^(B/(l[3,1])) <> one) and (g^(B/(l[4,1])) <> one) and (g^B = one) then
                #    break;
                #fi;
                if (g^B = one) then
                    break;
                fi;
            od;
        fi;

        if (g^B = one) then
            ppds := l[3];
            for i in ppds do
                if (i > 1) and ((q^(l[2])-1) mod i <> 0) then
                    for j in [1..d] do
                        if (B mod (i^j) = 0) and (g^(B/i^j) <> one) then
                            #Error("here");
                            foundFirst := true;
                            g := g^(B/i^j);
                            break;
                        fi; 
                    od;
                fi;
                if foundFirst then
                    break;
                fi;
            od;
        fi;
        counter := counter + 1;
        if foundFirst then
            break;
        fi;
    od;

    foundSecond := false;
    if foundFirst then
        counter := 1;
        while counter < 1000 do
            g2 := PseudoRandom(grp);
            B := 1;
            if (g2 <> one) then
                for l in ppdlist do
                    B := (q^(l[1])-1)*(q^(l[2])-1);
                    # This version works
                    #if (g2^(B/(l[3,1])) <> one) and (g2^(B/(l[4,1])) <> one) and (g2^B = one) then
                    #    break;
                    #fi;
                    if (g2^B = one) then
                        break;
                    fi;
                od;
            fi;

            if (g2^B = one) then
                ppds := l[3];
                for i in ppds do
                    if (i > 1) and ((q^(l[2])-1) mod i <> 0) then
                        for j in [1..d] do
                            if (B mod (i^j) = 0) and (g2^(B/i^j) <> one) then
                                foundSecond := true;
                                g2 := g2^(B/i^j);
                                break;
                            fi; 
                        od;
                    fi;
                    if foundSecond then
                        break;
                    fi;
                od;
            fi;
            counter := counter + 1;
            if foundSecond then
                break;
            fi;
        od;
    fi;

    if foundFirst and foundSecond then
        return [g,g2];
    fi;

    return fail;
end;


RECOG.BlaxBoxGoingDownStepVersion4_SL := function( grp, d, q )
local e, eprime, B, r, ppdlist, goode, i, j, ppds, f, p, factors, counter, l, one, foundFirst, foundSecond, g, g2, ppds2, min, max, h;

    # Start by preparing a list of good e and corresponding ppds
    factors := Factors(q);
    f := Size(factors);
    p := factors[1];
    one := One(grp);
    foundFirst := false;
    ppdlist := [];
    #goode := Log2Int(d);  ##Do we need this?

    if d <= 20 then
        min := 2;
        # 2*Log2Int(d)?
        max := Minimum([Log2Int(d), Int(d/2 - 1)]);
    else
        min := Log2Int(d);
        max := Minimum([5*Log2Int(d), Int(d/2 - 1)]);
    fi;
    
    # New test for making B smaller
    for e in [min..max] do
    #for e in [Maximum([2,Log2Int(d)])..Minimum([5*Log2Int(d), Int(d/2 - 1)])] do
        eprime := d - e;
        # Factors is bad since the numbers get too large. We need something else to find the ppds
        ppds := Factors(PrimitivePrimeDivisors(f*e,p).ppds);
        ##### Change 
        #ppds2 := Factors(PrimitivePrimeDivisors(f*eprime,p).ppds);
        #Add(ppdlist,[e,eprime,ppds,ppds2]);
        ppds := Collected(ppds);
        Add(ppdlist,[e,eprime,ppds]);
        #####
    od;

    counter := 1;
    while counter < 1000 do
        g := PseudoRandom(grp);
        B := 1;
        if (g <> one) then
            for l in ppdlist do
                B := (q^(l[1])-1)*(q^(l[2])-1);
                # This version works
                #if (g^(B/(l[3,1])) <> one) and (g^(B/(l[4,1])) <> one) and (g^B = one) then
                #    break;
                #fi;
                if (g^B = one) then
                    break;
                fi;
            od;
        fi;

        if (g^B = one) then
            ppds := l[3];
            for i in ppds do
                if (i[1] > 1) and ((q^(l[2])-1) mod i[1] <> 0) then
                    if (B mod (i[1]^(i[2])) = 0) and (g^(B/i[1]^(i[2])) <> one) then
                        #Error("here");
                        foundFirst := true;
                        g := g^(B/i[1]^(i[2]));
                    fi; 
                fi;
                if foundFirst then
                    break;
                fi;
            od;
        fi;
        counter := counter + 1;
        if foundFirst then
            break;
        fi;
    od;

    foundSecond := false;
    if foundFirst then
        counter := 1;
        while counter < 1000 do
            g2 := PseudoRandom(grp);
            B := 1;
            if (g2 <> one) then
                for l in ppdlist do
                    B := (q^(l[1])-1)*(q^(l[2])-1);
                    # This version works
                    #if (g2^(B/(l[3,1])) <> one) and (g2^(B/(l[4,1])) <> one) and (g2^B = one) then
                    #    break;
                    #fi;
                    if (g2^B = one) then
                        break;
                    fi;
                od;
            fi;

            if (g2^B = one) then
                ppds := l[3];
                for i in ppds do
                    if (i[1] > 1) and ((q^(l[2])-1) mod i[1] <> 0) then
                        if (B mod (i[1]^(i[2])) = 0) and (g2^(B/i[1]^(i[2])) <> one) then
                            #Error("here");
                            foundSecond := true;
                            g2 := g2^(B/i[1]^(i[2]));
                        fi; 
                    fi;
                    if foundSecond then
                        break;
                    fi;
                od;
            fi;
            counter := counter + 1;
            if foundSecond then
                break;
            fi;
        od;
    fi;

    if foundFirst and foundSecond then
        return [g,g2];
    fi;

    return fail;
end;


RECOG.BlaxBoxGoingDown_SL := function( grp, d, q )
local currentdim, eps, counter, currentgrp, res, testgrp, infos;

    currentdim := d;
    counter := 1;
    eps := 1000;
    currentgrp := grp;
    while (currentdim > 6) and (counter < eps) do
        res := RECOG.BlaxBoxGoingDownStepVersion4_SL(currentgrp, currentdim, q);

        if res <> fail then

            # For the next two lines we need a black box naming algorithm
            testgrp := RECOG.LinearActionRepresentation(GroupByGenerators(res)); 
            infos := RecogniseClassical(testgrp);

            # Bug in RecogniseClassical. GAP says its unknown but very often after a second run he knows that its a SL
            # (this bug only occurs for larger fields i.e. 2^8)
            if infos.isSLContained = "unknown" then
                infos := RecogniseClassical(testgrp);
                if infos.isSLContained = "unknown" then 
                    infos.isSLContained := false;
                fi;
            fi;

            if infos.isSLContained then
                currentgrp := GroupByGenerators(res);
                currentdim := Size(GeneratorsOfGroup(testgrp)[1]);
            fi;

        fi;
        Display("Infos about current state:");
        Print("currentdim: ");
        Display(currentdim);
        counter := counter + 1;
    od;

    return currentgrp;
end;


RECOG.BlackBoxFind2StingrayElement := function( grp, d, q )
local g, h, counter, epsilon, powercheck, factors, f, p, one, ppds2, ppdsD, B;
    
    factors := Factors(q);
    f := Size(factors);
    p := factors[1];
    one := One(grp);
    epsilon := 1000;
    counter := 1;
    
    # Initilize PPDs
    ppds2 := PrimitivePrimeDivisors(f*2,p).ppds;
    if (d mod 2 = 1) then
        powercheck := (q^2-1)*(q^(d-2)-1)*q;
        #powercheck := (q^2-1)*(q^(d-2)-1);
        ppdsD := PrimitivePrimeDivisors(f*(d-2),p).ppds;
    else
        powercheck := (q^2-1)*(q^(d-3)-1)*q;
        #powercheck := (q^2-1)*(q^(d-3)-1);
        ppdsD := PrimitivePrimeDivisors(f*(d-3),p).ppds;
    fi;
    B := powercheck/(ppds2*ppdsD);
    Print("check 1");

    while counter < epsilon do
        g := PseudoRandom(grp);
        Print("check 2");
        if g^powercheck = one then
            Print("check 3");
            h := g^B;
            Print("check 4");
            if h <> one then
                h := h^ppdsD;
                Print("check 5");
                if h <> one then
                    return h;
                fi;
            fi;
        fi;
        counter := counter + 1;
    od;

    return fail;

end;



RECOG.BlackBoxFind2StingrayElementVersion2 := function( grp, d, q )
local g, h, counter, epsilon, powercheck, factors, f, p, one, ppds2, ppdsD, B, l, testvalue;
    
    factors := Factors(q);
    f := Size(factors);
    p := factors[1];
    one := One(grp);
    epsilon := 1000;
    counter := 1;
    
    # Initilize PPDs
    ppds2 := PrimitivePrimeDivisors(f*2,p).ppds;
    if (d mod 2 = 1) then
        powercheck := (q^2-1)*(q^d-1);
        ppdsD := PrimitivePrimeDivisors(f*d,p).ppds;
    else
        powercheck := (q^2-1)*(q^(d-1)-1);
        ppdsD := PrimitivePrimeDivisors(f*(d-1),p).ppds;
    fi;

        #Test
        powercheck := (q^2-1)*(q^(d-2)-1);
        ppdsD := PrimitivePrimeDivisors(f*(d-2),p).ppds;
        testvalue := (q^(d-2)-1)/Gcd((q^2-1)/ppds2,Gcd(q^2-1,q^(d-2)-1));

    B := powercheck/(ppds2);

    while counter < epsilon do
        g := PseudoRandom(grp);
        if g^powercheck = one then
            if g^(powercheck/ppdsD) <> one and g^(powercheck/ppds2) <> one then
                h := g^testvalue;
                if h <> one then
                    return h;
                fi;
            fi;
        fi;
        counter := counter + 1;
    od;

    return fail;

end;



RECOG.BlaxBoxFindSL4 := function( grp, d, q )
local s1, s2, H, check, testgrp, infos;

    s1 := RECOG.BlackBoxFind2StingrayElement(grp, d, q);
    check := false;

    repeat
        s2 := RECOG.BlackBoxFind2StingrayElement(grp, d, q);
        H := GroupByGenerators([s1,s2]);

        # For the next two lines we need a black box naming algorithm
        testgrp := RECOG.LinearActionRepresentation(H); 
        if NumberRows(GeneratorsOfGroup(testgrp)[1]) = 4 then
            infos := RecogniseClassical(testgrp);

            # Bug in RecogniseClassical. GAP says its unknown but very often after a second run he knows that its a SL
            # (this bug only occurs for larger fields i.e. 2^8)
            if infos.isSLContained = "unknown" then
                infos.isSLContained := false;
            fi;

            if infos.isSLContained then
                check := true;
            fi;
        fi;
    until check;

    return GroupByGenerators([s1,s2]);

end;