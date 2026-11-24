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
##  The algorithms use group operations, random elements, and element
##  orders, so these functions work for G given as a black box
##  group isomorphic to SL(3,q); this is also why the field size q is
##  passed explicitly rather than being extracted from G.
##  For q > 11, the function returns SL(2,q) or fail if the search is
##  unsuccessful. The small-field strategy can return a proper subgroup.
##  
##      
##
#############################################################################

# RECOG.SL3GoingDown( G, q ), for odd q > 11.
#
# Following Frank Luebeck's approach, use a power x^(q+1) that
# acts as a scalar on a plane.
RECOG.SL3GoingDown := function(G, q)
    local attempt, x, power, t, conjugate, commutator, gens, pr,
          i, order, foundSplit, foundNonsplit;

    for attempt in [1..40] do
        # The two power tests force semisimple type 2+1 in SL(3,q).
        # An irreducible element has order dividing q^2+q+1,
        # whose gcd with q^2-1 divides q-1.
        x := PseudoRandom(G);
        power := x^(q-1);
        if IsOne(power) or not IsOne(power^(q+1)) then
            continue;
        fi;

        # The power t = x^(q+1) acts as a scalar on a plane.
        # If t is scalar on the whole space, the commutator is trivial.
        # With two distinct eigenvalues, t and its conjugate each have
        # an eigenplane and an eigenline. The derived subgroup of
        # <t, conjugate> fixes the intersection of the planes pointwise
        # and preserves the span of the two eigenlines. If these spaces
        # are complementary, the derived subgroup lies in an embedded
        # SL(2,q). In the remaining cases, t and its conjugate preserve
        # a full flag, so the derived subgroup is unipotent.
        t := power * x^2;
        conjugate := t^PseudoRandom(G);
        commutator := Comm(t, conjugate);
        if IsOne(commutator) then
            continue;
        fi;

        # For q > 11, both orders certify that this is SL(2,q).
        gens := [commutator, commutator^t, commutator^conjugate];
        pr := ProductReplacer(gens);
        foundSplit := false;
        foundNonsplit := false;
        for i in [1..20] do
            order := Order(Next(pr));
            if order = q-1 then
                foundSplit := true;
            elif order = q+1 then
                foundNonsplit := true;
            fi;
            if foundSplit and foundNonsplit then
                return SubgroupNC(G, gens);
            fi;
        od;
    od;
    return fail;
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

    s := SubgroupNC(G, list);
    return s;
end;

# RECOG.FindSL2inSL3( G, q )
#
# Main entry point. Dispatches to the heuristic SL3GoingDown_SmallQ for
# q <= 11 and to SL3GoingDown otherwise. The latter can return fail.
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
