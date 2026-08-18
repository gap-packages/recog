###############################################################################
##
##  Authors: Till Eisenbrand
##           Underlying ideas due to Frank Luebeck (SL3GoingDown)
##           and Till Eisenbrand (SL3GoingDown_SmallQ).
##
##  Main function:  RECOG.FindSL2inSL3(G, q)
##
##  Given G isomorphic to SL(3,q) for an odd prime power q, finds an
##  embedded copy of SL(2,q) inside G, using one of two strategies 
##  depending on the size of q (see comments below for details).
##
##  Note: G is only ever accessed via PseudoRandom, ProductReplacer, and
##  Order. Hence these functions work for G given as a black box
##  group isomorphic to SL(3,q); this is also why the field size q is
##  passed explicitly rather than being extracted from G.
##  Additionally, the output is a group that SHOULD be isomorphic to SL(2,q). 
##  The probability that the function RECOG.FindSL2inSL3 succeeds is > 0.95 
##  according to benchmarks.
##  
##      
##
#############################################################################

# RECOG.SL3GoingDown( G, q )
#
# Strategy due to Frank Luebeck.
# t := PseudoRandom(G)^(q+1) quite often has two equal eigenvalues.
# Then u := <t, t^rand> is almost always isomorphic to GL(2,q), 
# and its derived subgroup is often isomorphic to SL(2,q). Here the
# derived subgroup is approximated via random commutators.
RECOG.SL3GoingDown := function(G, q)
    local t, rand, u, s, list, x, y, i, order, count, attempt,
          isSL3, hasElementOfOrderQPlus1, hasElementOfOrderQMinus1,
          ppds2, ppds3, p, foundSL2, MAX_ATTEMPTS, INNER_ATTEMPTS;

    MAX_ATTEMPTS := 20;
    INNER_ATTEMPTS := 20;

    ppds3 := Factors(PrimitivePrimeDivisors(3, q).ppds);

    attempt := 0;
    repeat
        foundSL2 := false;
        attempt := attempt + 1;

        # Construct a candidate subgroup u, then approximate its derived
        # subgroup s via random commutators.
        t := PseudoRandom(G)^(q+1);
        rand := PseudoRandom(G);
        u := Subgroup(G, [t, t^rand]);

        list := [];
        for i in [1 .. 10] do
            x := PseudoRandom(u);
            y := PseudoRandom(u);
            Add(list, Comm(x, y));
        od;
        s := Subgroup(G, list);

        # Check (1): rule out that s is (isomorphic to) SL(3,q) rather
        # than SL(2,q), by searching for an element whose order is
        # divisible by a primitive prime divisor of q^3-1.
        isSL3 := false;
        count := 0;
        repeat
            count := count + 1;
            order := Order(PseudoRandom(s));
            for p in ppds3 do
                if 0 = order mod p then
                    isSL3 := true;
                fi;
            od;
        until isSL3 or count > INNER_ATTEMPTS;

        # Check (2): if s does not look like SL(3,q), look for elements
        # of order q+1 and q-1, both of which occur in SL(2,q).
        if not isSL3 then
            hasElementOfOrderQPlus1 := false;
            hasElementOfOrderQMinus1 := false;
            count := 0;
            repeat
                count := count + 1;
                order := Order(PseudoRandom(s));
                if order = q + 1 then
                    hasElementOfOrderQPlus1 := true;
                elif order = q - 1 then
                    hasElementOfOrderQMinus1 := true;
                fi;
                if hasElementOfOrderQPlus1 and hasElementOfOrderQMinus1 then 
                    foundSL2 := true;
                fi;
            until foundSL2 or count > INNER_ATTEMPTS;
        fi;

    until foundSL2 or attempt > MAX_ATTEMPTS;
    return s;
end;

# RECOG.SL3GoingDown_SmallQ( G, q )
#
# Strategy due to Till Eisenbrand.
# Finds an involution g in G via RECOG.InvolutionSearcher, computes its
# centraliser C := C_G(g) (isomorphic to S(GL(2,q) x F_q^*)) via
# RECOG.InvolutionCentraliser, and approximates the derived subgroup of C
# via random commutators in C.
RECOG.SL3GoingDown_SmallQ := function(G, q)
    local g, ord, C, i, list, s, pr, x, y;

    pr := ProductReplacer(GeneratorsOfGroup(G));
    ord := Order;

    g := RECOG.InvolutionSearcher(pr, ord, 20);
    C := RECOG.InvolutionCentraliser(pr, ord, g, 6);

    list := [];
    for i in [1 .. 10] do
        x := PseudoRandom(C);
        y := PseudoRandom(C);
        Add(list, Comm(x, y));
    od;

    s := Subgroup(G, list);
    return s;
end;

# RECOG.FindSL2inSL3( G, q )
#
# Main entry point. Dispatches to SL3GoingDown_SmallQ for small odd q,
# and to SL3GoingDown otherwise. Note that this function may falsely return 
# a subgroup which is not isomorphic to SL(2,q).
RECOG.FindSL2inSL3 := function(G, q)

    if not IsPrimePowerInt(q) or q mod 2 = 0 then
        Error("RECOG.FindSL2inSL3: <q> must be a prime power");
    fi;
    if q mod 2 = 0 then
        Error("RECOG.FindSL2inSL3: q must be odd");
    fi;

    if q <= 11 then
        return RECOG.SL3GoingDown_SmallQ(G, q);
    else
        return RECOG.SL3GoingDown(G, q);
    fi;
end;
