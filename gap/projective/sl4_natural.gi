###############################################################################
##
##  Authors: Till Eisenbrand
##           The underlying algorithm is due to Daniel Rademacher; see
##           Algorithm 15 ("GoingDownFinalStepSL") in:
##           D. Rademacher, "Constructive Recognition of Finite Classical Groups with
##           Stingray Elements", Ph.D. thesis, RWTH Aachen University, Germany, 2024.
##
##
##  This file provides the function:
##
##    RECOG.FindSL2inSL4_natural(G, N)
##
##  Purpose:
##    Given G = SL(4,q) (q odd), this function finds an embedded copy of
##    SL(2,q) inside G as a "stingray subgroup".  Concretely, it looks for
##    a base change matrix  bas  such that, in the new basis, the found
##    subgroup consists of block matrices of the form
##
##        [ A | 0 ]
##        [ 0 | I ]      with  A in SL(2,q).
##
##    The function proceeds by:
##      1. Searching for a strong pre-involution  t  of type 2+2, i.e. a
##         non-trivial involution with dim(E_1(t)) = dim(E_{-1}(t)) = 2.
##      2. Building a base change from the eigenspaces of  t.
##      3. Drawing random elements from the centraliser C_G(t) via the Bray
##         trick (RECOG.CentralisingElementOfInvolution) and filtering for
##         those that act trivially on the lower 2x2 block in the new basis.
##         Such elements generate the stingray-embedded SL(2,q).
##      4. Stopping as soon as the collected generators are recognised
##         (non-constructively) as SL(2,q).
##
##  Input:
##    G  -- a matrix group equal to SL(4,q) for some odd prime power q,
##           given by 4x4 matrices over GF(q).
##    N  -- positive integer: random-element budget.
##
##  Returns:
##    "fail"  if the budget N is exhausted before success, OR a record with
##    the following fields:
##
##      .U     -- a subgroup of G with U isomorphic to SL(2,q), stingray
##                embedded in G with respect to the base change bas.
##      .bas   -- the 4x4 base change matrix bas such that  u^bas
##                is block-diagonal diag(A, I_2) for every u in U.
##      .gens  -- list of generators of U as elements of G (i.e. 4x4
##                matrices over GF(q)).
##      .Nout  -- remaining budget after completion  (N - number of random
##                selections actually used).
##
#############################################################################


RECOG.FindSL2inSL4_natural := function(G, N)
    local F, q, one, gens_group, gens_bas, 
          pr, t, basis1, basism1, bas, basInv,
          h, hb, topLeft, bottomRight, ordr, ordu, K, Nstart,
          U, readyqm1, readyqpl1, count, image, u;

    
    F := FieldOfMatrixGroup(G);
    q := Size(F);
    one := IdentityMat(4, F);
    Nstart := N;

    if DimensionOfMatrixGroup(G) <> 4 then
        Error("FindSL2inSL4: <G> must act in dimension 4");
    fi;
    if q mod 2 = 0 then
        Error("FindSL2inSL4: q must be odd");
    fi;

    pr := ProductReplacer(GeneratorsOfGroup(G));

    # find a strong pre-involution: t = x^(|x|/2) of type 2+2.
    # RECOG.InvolutionSearcher(pr,ord,0) uses exactly one Next(pr).
    while N > 0 do
        t := RECOG.InvolutionSearcher(pr, Order, 0);
        N := N - 1;
        if t <> fail then
            basis1 := RECOG.FixspaceMat(t); # note that RECOG.FixspaceMat works with elements with memory too
            if Length(basis1) = 2 then
                break;
            fi;
        fi;
    od;

    if N = 0 then
        Info(InfoRecog, 2, "FindSL2inSL4: out of budget while looking for a strong pre-involution");
        return fail;
    fi;

    basism1 := RECOG.EigenspaceMat(t, -One(F));
    basInv := Concatenation(basis1, basism1);
    bas := basInv^-1;

    gens_bas := [];
    gens_group := [];

    while N > 0 do
        h := RECOG.CentralisingElementOfInvolution(pr, Order, t);
        N := N - 1;

        hb := basInv * h * bas;
        topLeft := hb{[1,2]}{[1,2]};
        bottomRight := hb{[3,4]}{[3,4]};

        ordr := Order(bottomRight);
        topLeft := topLeft^ordr;
        if not IsOne(topLeft) then
            Add(gens_bas, topLeft);
            Add(gens_group, h^ordr);

            # nur die letzten k Erzeuger zum Testen benutzen
            if Length(gens_bas) > 2 then
                image := Group(gens_bas);
                readyqm1 := false;
                readyqpl1 := false;
                count := 0;
                repeat
                    u := PseudoRandom(image);
                    ordu := Order(u);
                    if ordu = q-1 then readyqm1 := true; fi;
                    if ordu = q+1 then readyqpl1 := true; fi;
                    count := count + 1;
                until (readyqm1 and readyqpl1) or count = 20;

                if readyqm1 and readyqpl1 then
                    U := Group(gens_group);
                    return rec(U := U, bas := bas, gens := gens_group, Nout := N);
                fi;
            fi;
        fi;
    od;
    return fail;
end;
