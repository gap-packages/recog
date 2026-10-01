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
######## Constructive Recognition of Sp(4,q) ################################
#############################################################################
#############################################################################


# The functions described here follow "Fast constructive recognition of black box symplectic groups" by Peter A. Brooksbank 
# (Journal of Algebra, Volume 320 (2008), 885 - 909.) in the following [Brooksbank]
# and the dissertation "Constructive recognition of classical groups of small rank" by Kenneth J. Clarkson (student of Eamonn O'Brien) in the following [Clarkson].
# The functions implemented here are from page 60 to 63 of [Clarkson]

# In some situations the implementation differ from [Clarkson] since the computational results did not completly compare to the theoretical results.
# These situation are marked by [[DIFFERENCE]]


# Main function which basically implements the summary described at page 60 of [Clarkson] i.e. Section 5.2.1 
RECOG.FindStdGensSp4 := function(G, d, q)
local K, twofactors, stdgens1, stdgens2, factor1Gens, factor2Gens, p, f, stdgens1Complete, stdgens2Complete, basechange, basechangelift, slpgens1, slpgens2, myslp,
t1, h1, s1, t0, t2, h2, s2, T, gensT, currentbc, i, g, foundEle, zeroBlock, t, L, v, slp, slp1, slp2, newgens, t1l, t2l, slpL, slpG, listGeneratorsL, LL, hom, wh, basis,
Lbc, LGens, stdgensL, stdgensLComplete, tg, omega, h, space1, space2, hbig, u0, u, PermMat, LGensBig, space1Copy, check, basechangeSLs, form, formbc, GG, j, diagele,
vGood, x1, x2, x3, l1, x, mid, newgens1, newgens2, slpnewgens, allout, slpnewgensC, correct, uu, vv, connectG, transdown, transup, transdiag, transdiag2, coeff, val;

    # Initilize basis parameters
    f := Factors(q);
    p := f[1];
    f := Size(f);
    omega := PrimitiveElement(GF(q));

    # Set up the SLP
    if not(IsObjWithMemory(GeneratorsOfGroup(G)[1])) then
        G := GroupWithMemory(G);
    fi;
    
    # Corresponds exactly to 5.2.2 of [Clarkson]
    Info(InfoRecog,2,"Construct subgroup K which is isomorphic to SL(2,q) x SL(2,q)");
    if (q mod 2 = 0) then
        K := RECOG.ConstructKEven(G, q);
    else
        K := RECOG.ConstructKOdd(G, q);
    fi;

    #slp := K[2];
    K := K[1];

    # Extracting the two factors is done by the methods descibed by Leedham-Green and O'Brien in "Constructive recognition of classical groups in odd characteristic"
    # Section 11
    # Note that the method for even involutions is not implemented in GAP yet and so there is no method for extracting the two factors in even characteristic
    Info(InfoRecog,2,"Extract the two SL(2,q) factors of K");
    twofactors := RECOG.ExtractTwoSL2Factors(K,q);
    if twofactors = fail then
        return TemporaryFailure;
    fi;
    basechange := twofactors[5];

    slp1 := SLPOfElms([twofactors[1,1],twofactors[1,2]]);
    slp2 := SLPOfElms([twofactors[2,1],twofactors[2,2]]);

    # [[DIFFERENCE]] Note mentioned in [Clarkson] but we apply an additional basechange to later have the natural Sp(4,q) of GAP
    form := PreservedSesquilinearForms(G^(basechange^(-1)))[1];
    formbc := BaseChangeToCanonical(form);
    #GG := G^(basechange^(-1)*formbc^(-1));

    factor1Gens := [(twofactors[1,1]^(basechange^(-1)*formbc^(-1))){[3,4]}{[3,4]},(twofactors[1,2]^(basechange^(-1)*formbc^(-1))){[3,4]}{[3,4]}];
    factor2Gens := [(twofactors[2,1]^(basechange^(-1)*formbc^(-1))){[1,2]}{[1,2]},(twofactors[2,2]^(basechange^(-1)*formbc^(-1))){[1,2]}{[1,2]}];

    # Call constructive recognition on the two SL(2,q) copies p. 61 middle of [Clarkson]
    Info(InfoRecog,2,"Perform constructive recognition on both copies of SL(2,q)");
    stdgens1 := RECOG.ConstructiveRecognitionSL2NaturalRepresentation(GroupByGenerators(factor1Gens),q, 0.001);
    stdgens1Complete := RECOG.ConstructiveRecognitionSL2NaturalRepresentationCompleteBasis(stdgens1[1],GF(q),q,p,f);
    slpgens1 := CompositionOfStraightLinePrograms(stdgens1Complete[2],stdgens1[3]);
    stdgens1Complete := stdgens1Complete[1];

    stdgens2 := RECOG.ConstructiveRecognitionSL2NaturalRepresentation(GroupByGenerators(factor2Gens),q, 0.001);
    stdgens2Complete := RECOG.ConstructiveRecognitionSL2NaturalRepresentationCompleteBasis(stdgens2[1],GF(q),q,p,f);
    slpgens2 := CompositionOfStraightLinePrograms(stdgens2Complete[2],stdgens2[3]);
    stdgens2Complete := stdgens2Complete[1];

    slp := IntegratedStraightLineProgram([CompositionOfStraightLinePrograms(slpgens1,slp1),CompositionOfStraightLinePrograms(slpgens2,slp2)]);
    slpnewgensC := IntegratedStraightLineProgram([CompositionOfStraightLinePrograms(slpgens1,slp1),CompositionOfStraightLinePrograms(slpgens2,slp2)]);

    basechangelift := RECOG.LiftGroup([formbc*basechange],4,q,d);
    basechangeSLs := IdentityMat(d,GF(q));
    basechangeSLs{[3,4]}{[3,4]} := stdgens1[2];
    basechangeSLs{[1,2]}{[1,2]} := stdgens2[2];

    currentbc := basechangeSLs * basechangelift[2,1];

    # Continue now with 5.2.3 
    # Set up new SLPs for writing specific elements as words
    # Construct Elements in std copies. Also write MSLP for these elements
    newgens1 := StripMemory(stdgens1Complete);
    newgens1 := Concatenation([newgens1[1]],newgens1[2],newgens1[3]);
    newgens2 := StripMemory(stdgens1Complete);
    newgens2 := Concatenation([newgens2[1]],newgens2[2],newgens2[3]);
    for i in [1..Size(newgens1)] do
        g := IdentityMat(4,GF(q));
        g{[3,4]}{[3,4]} := newgens1[i];
        newgens1[i] := g;
        g := IdentityMat(4,GF(q));
        g{[1,2]}{[1,2]} := newgens2[i];
        newgens2[i] := g;
    od;
    newgens := Concatenation(newgens1,newgens2,GeneratorsOfGroup(G^((currentbc{[1..4]}{[1..4]})^(-1))));
    GG := GeneratorsWithMemory(newgens);
    mid := Size(newgens1);

    t1 := GG[mid+2];
    t2 := GG[2];
    h1 := GG[mid+1];
    h2 := GG[1];
    t0 := GG[2+f];
    t1l := GG[mid+2+f];
    t2l := GG[2+f];
    s1 := t1*(t1l)^(-1)*t1;
    s2 := t2*(t2l)^(-1)*t2;

    # Construct the group T
    Info(InfoRecog,2,"Construct subgroup T which intersects both SL copies");
    gensT := [t1];
    for i in [1..(f-1)] do
        Add(gensT, t1^(h1^i));
    od;
    T := GroupByGenerators(gensT);
    zeroBlock := 0 * IdentityMat(2,GF(q));

    # Find specific g in G (see 5.2.3 point 2. of [Clarkson])
    # TODO: Can we always iterate over the generators of G?!? ----> No, generators are not good enough (take random elements here)
    foundEle := false;
    for i in [(2*mid+1)..Size(newgens)] do
        g := GG[i];
        L := GeneratorsOfGroup(T^g);
        for tg in L do
            if ((tg){[1,2]}{[3,4]} <> zeroBlock or (tg){[3,4]}{[1,2]} <> zeroBlock) and not ForAll(gensT,t -> tg*t= t*tg ) then
                foundEle := true;
                break;
            fi;
        od;
        if foundEle then
            break;
        fi;
    od;

    if not(foundEle) then
        Display("TODO: maybe we have to look at this again.");
        return fail;
    fi;

    # Set up the group L and call constructive recognition on it (see 5.2.3 point 3. of [Clarkson])
    Info(InfoRecog,2,"Identity an element h of Q");
    # ClosureGroup(T,T^g)???
    L := GroupByGenerators(Concatenation(GeneratorsOfGroup(T),GeneratorsOfGroup(T^g)));
    Lbc := RECOG.ComputeBlockBaseChangeMatrix(GeneratorsOfGroup(L),4,q);
    LGensBig := GeneratorsOfGroup(L^(Lbc^(-1)));
    LGens := [1..Size(LGensBig)];
    for i in [1..Size(LGensBig)] do 
            LGens[i] := (LGensBig[i]){[1,2]}{[1,2]};
    od;
    stdgensL := RECOG.ConstructiveRecognitionSL2NaturalRepresentation(GroupByGenerators(LGens),q,0.001);
    stdgensLComplete := RECOG.ConstructiveRecognitionSL2NaturalRepresentationCompleteBasis(stdgensL[1],GF(q),q,p,f);
    slpL := CompositionOfStraightLinePrograms(stdgensLComplete[2],stdgensL[3]);
    stdgensLComplete := stdgensLComplete[1];

    slpL := CompositionOfStraightLinePrograms(slpL,SLPOfElms(GeneratorsOfGroup(L)));
    slpG := [];
    connectG := [];
    for i in [1..Size(GeneratorsOfGroup(G))] do
        Add(slpG,[i,1]);
        Add(connectG,[i,1]);
    od;

    Add(slpG,connectG);
    slpG := StraightLineProgram(slpG,Size(GeneratorsOfGroup(G)));
    slp := CompositionOfStraightLinePrograms(slpL,IntegratedStraightLineProgram([slp,slpG]));

    # Construct normalising element of T and T^g and of order q-1 (see 5.2.3 point 4. of [Clarkson])
    # TODO: choose first and f+1 ?
    space1 := RECOG.FixspaceMat(LGens[1]^(stdgensL[2]^(-1))); 
    space1 := MutableCopyMat(space1);
    for i in [2..Size(LGens)] do
        space2 := RECOG.FixspaceMat(LGens[i]^(stdgensL[2]^(-1))); 
        Append(space1,space2);
        if NullspaceMat(space1) = [] then
            break;
        else
            Remove(space1,2);
        fi;
    od;

    h := IdentityMat(2,GF(q));
    h[1,1] := omega;
    h[2,2] := omega^(-1);
    h := space1^(-1)*h*space1;

    # Write h in terms of the standard generators
    wh := RECOG.RewritingSL2(stdgensLComplete,GF(q),q,p,f,h);
    hbig := IdentityMat(4,GF(q));
    hbig{[1..2]}{[1..2]} := h^(stdgensL[2]);
    h := hbig^Lbc;
    slp := CompositionOfStraightLinePrograms(wh,slp);
    
    # Now we can finally write the standard generators of Sp(4,q)
    Info(InfoRecog,2,"Combine everything for the standard generators of Sp(4,q)");

    # Initilise the needed elements with SLPs
    newgens := Concatenation(newgens1,newgens2,[h],GeneratorsOfGroup(G^((currentbc{[1..4]}{[1..4]})^(-1))));
    GG := GeneratorsWithMemory(newgens);

    t1 := GG[mid+2];
    t2 := GG[2];
    h1 := GG[mid+1];
    h2 := GG[1];
    t0 := GG[2+f];
    t1l := GG[mid+2+f];
    t2l := GG[2+f];
    s1 := t1*(t1l)^(-1)*t1;
    s2 := t2*(t2l)^(-1)*t2;
    h := GG[2*mid+1];

    # Construct u0 (see 5.2.3 point 5. of [Clarkson])
    u0 := Comm(h,h1);

    #From now one we follow 5.2.5 of [Clarkson]

    # [[DIFFERENCE]] u is definetly not the element as mentioned in [Clarkson]. Sometimes it is even the identity.
    # We use some trick from Magma even though our approach still slightly differs.
    # It should also be mentioned, that u actually looks like v and v looks like u with respect to the elements in [Clarkson]
    u := Comm(Comm(u0,t0),h2);

    #u := Comm(Comm(u0,s2),h2);

    if u = One(G) then
        u := Comm(u0,h2);
    fi;

    # [[DIFFERENCE]] Our u somehow does not have trivial entries. We fix that here even though it is not mentioned in [Clarkson]
    # TODO: How to avoid next discrete logarithm?!?! Possible?
    # Note: Discrete logarithm is not really crucial, since the algorithm uses an SL2 oracle which so far (2023) requires also a discrete logarithm oracle
    correct := LogFFE(u[1,3],h1[1,1]);
    u := u^(h1^correct);

    # Set up a last base change to the natural representation of GAP
    PermMat := PermutationMat((2,4),d,GF(q));
    PermMat[2,4] := -1*One(GF(q));

    currentbc := PermMat*currentbc;

    # [[DIFFERENCE]] Now we are following 5.2.5 of [Clarkson] even though we swap u and v by setting uu := v and vv := u
    v := u^s2;
    if IsEvenInt(q) then
        t := u*Comm(t0,v);
    else
        t := Comm(u,v);
    fi;
    uu := v;
    vv := u;
    l1 := s1;
    x := uu^(s2^2);
    x1 := x^l1;
    x2 := x^s2;
    x3 := (x1)^s2;
    t1 := Comm(x1,x2);

    vGood := s2^2*(x1^3*t1)^3;

    transdown := [u^(s1^(-1))];
    transup := [transdown[1]^(vGood^s1)];
    transdiag := [t^((q+1)/2)];
    transdiag2 := [t^((q+1)/2)];

    if f > 1 then
        for i in [1..(f-1)] do
            Add(transup,transup[1]^(h1^(-i)));
            Add(transdown,transup[i+1]^(vGood^s1));
            Add(transdiag,transdiag[1]^(h1^(-i)));
        od;

        basis := [1..f];
        for i in [0..f-1] do
            basis[i+1] := omega^(2*i);
        od;
        basis := Basis(GF(q),basis);
        for i in [1..(f-1)] do
            coeff := Coefficients(basis,omega^i);
            diagele := s1^0;
            for j in [1..f] do
                val := Int(coeff[j]);
                diagele := diagele * transdiag[j]^(val);
            od;
            Add(transdiag2,diagele);
        od;
    fi;

    transup := Concatenation(transup,transdown);
    transup := Concatenation(transup,transdiag2);

    slp := CompositionOfStraightLinePrograms(SLPOfElms(Concatenation(transup,[vGood^s1,vGood^s1,s1,h1])),IntegratedStraightLineProgram([slpnewgensC,slp,slpG]));

    return [StripMemory([s1^(PermMat^(-1)),t^(PermMat^(-1)),h1^(PermMat^(-1)),u^(PermMat^(-1)),vGood^(PermMat^(-1))]),currentbc,slp];
end;



# # Used by RECOG.ConstructKEven
# RECOG.IsSp4SmallPP2K := function(tau,q,list)
# local entry, ppd4k, ord, prime, ppds, i;

#     if q = 8 then
#         #ord := RECOG.EstimateOrder(tau);
#         if (Order(tau) mod 21 = 0) then
#             return true;
#         else
#             return false;
#         fi;
#     elif q = 2 then
#         if (Order(tau) mod 3 = 0) then
#             return true;
#         else
#             return false;
#         fi;
#     else
#         ord := Order(tau);
#         for i in list do
#             if (ord mod i = 0) then
#                 return true;
#             fi;
#         od;
#         return false;
#     fi;

# end;



# # Used by RECOG.ConstructKOdd
# RECOG.IsSp4SmallPP4K := function(tau,q,list)
# local entry, ppd4k, ord, prime;

#     ord := Order(tau);
#     if (ord mod q = 0) then
#         for entry in list do
#             ppd4k := entry[2];
#             for prime in ppd4k do
#                 if (ord mod prime = 0) then
#                     return true;
#                 fi;
#             od;
#         od;
#     else
#         return false;
#     fi;

#     return false;

# end;



# # Corresponds exactly to 5.2.2 of [Clarkson]
# RECOG.ConstructKEven := function(h, q)
# local a, tau, g, K0, Knext, S, counter, p, preparelist, i, containsPPD2K, containsPPD4K, ppd, new, k, ppds;

#     counter := 1;
#     k := Size(Factors(q));
#     ppds := Factors(PrimitivePrimeDivisors(2*k,2).ppds);

#     Info(InfoRecog,2,"Function: ConstructKEven");
#     Info(InfoRecog,2,"Try to compute tau");

#     while counter < 100 do
#         tau := PseudoRandom(h);
#         if RECOG.IsSp4SmallPP2K(tau,q,ppds) and ((tau^(q-1)) <> 1) then
#             a := tau^(q-1);
#             #a := tau^(2*(q^2-q+1));
#             Info(InfoRecog,2,"Found tau");
#             while counter < 100 do
#                 g := PseudoRandom(h);
#                 K0 := GroupByGenerators([a,a^g]);
#                 # Magma uses another hack here but just checking that K0 = SL2 x SL2
#                 # We should probably also use it here
#                 Knext := RECOG.DerivedSubgroupMonteCarlo(K0,20);
#                 while not(IsTrivial(Knext)) do
#                     K0 := Knext;
#                     Knext := RECOG.DerivedSubgroupMonteCarlo(K0,20);
#                 od;
#                 S := [1..Int(8*(Log2Int(q)+1))];
#                 for i in [1..Size(S)] do
#                     S[i] := PseudoRandom(K0);
#                 od;
#                 containsPPD2K := false;
#                 containsPPD4K := false;

#                 for i in S do

#                     if RECOG.IsSp4SmallPP2K(tau,q,ppds) then
#                         containsPPD2K := true;
#                     fi;

#                     if RECOG.IsSp4SmallPP4K(tau,q,ppds) then
#                         containsPPD4K := true;
#                     fi;

#                 od;

#                 if containsPPD2K and not(containsPPD4K) then
#                     return [K0,SLPOfElms(GeneratorsOfGroup(K0))];
#                 fi;

#                 if counter = 5 then
#                     Error("here");
#                 fi;

#                 counter := counter + 1;
#             od;
#         fi;
#         counter := counter + 1;
#     od;

#     if counter >= 100 then
#         return fail;
#     fi;

# end;


# # Corresponds exactly to 5.2.2 of [Clarkson]
# RECOG.ConstructKOdd := function(G, q)
# local count, tau, order, centre, n, taun, K0, K, CentralElement, g;

#     count := 0;
    
#     #TODO: Don't have do compute this right? Always the same two diagonal matrices
    
#     while count < 30 do
#         tau := PseudoRandom(G);
#         order := Order(tau);
#         if (order mod 2 = 0) then
#             n := order/2;
#             taun := tau^n;
#             CentralElement := true;
#             for g in GeneratorsOfGroup(G) do
#                 if g*taun*g^(-1) <> taun then
#                     CentralElement := false;
#                     break;
#                 fi;
#             od;
#             if not(CentralElement) then
#                 K0 := GroupByGenerators(RECOG.CentraliserOfInvolution(G,taun,[],true,100,RECOG.CompletionCheck,PseudoRandom)[1]);
#                 K := RECOG.DerivedSubgroupMonteCarlo(K0,20);
#                 return [K,SLPOfElms(GeneratorsOfGroup(K))];
#             fi;
#         fi;;
#         count := count + 1;
#     od;

#     return fail;
# end;



RECOG.IsSp4SmallPP2K := function(tau,q,list)
local entry, ppd4k, ord, prime;

    ord := Order(tau);
    if (ord mod q = 0) then
        for entry in list do
            ppd4k := entry[2];
            for prime in ppd4k do
                if (ord mod prime = 0) then
                    return true;
                fi;
            od;
        od;
    else
        return false;
    fi;

    return false;

end;



RECOG.IsSp4SmallPP4K := function(tau,q,list)
local entry, ppd4k, ord, prime;

    ord := Order(tau);
    if (ord mod q = 0) then
        for entry in list do
            ppd4k := entry[2];
            for prime in ppd4k do
                if (ord mod prime = 0) then
                    return true;
                fi;
            od;
        od;
    else
        return false;
    fi;

    return false;

end;



RECOG.ConstructKEven := function(h, q)
local a, tau, g, K0, Knext, S, counter, p, preparelist, i, containsPPD2K, containsPPD4K, ppd, new, k;

    counter := 1;

    preparelist := [];
    p := Factors(q)[1];
    # TODO: Adjust to ppd# elements. See Dissertation Jenneth Klarkson (Eamonns student)
    for k in [1..10] do
        new := [k];
        ppd := PrimitivePrimeDivisors( 2*k, p );
        Add(new,DuplicateFreeList(Factors(ppd.ppds)));
        ppd := PrimitivePrimeDivisors( 4*k, p );
        Add(new,DuplicateFreeList(Factors(ppd.ppds)));
        Add(preparelist,new);
    od;

    Info(InfoRecog,2,"Precomputation finished");

    while counter < 100 do
        tau := PseudoRandom(h);
        if RECOG.IsSp4SmallPP2K(tau,q,preparelist) and ((tau^(q-1)) <> 1) then
            a := tau^(q-1);
            #a := tau^(2*(q^2-q+1));
            Info(InfoRecog,2,"Found tau");
            while counter < 100 do
                g := PseudoRandom(h);
                K0 := GroupByGenerators([a,a^g]);
                Knext := RECOG.DerivedSubgroupMonteCarlo(K0,20);
                while not(IsTrivial(Knext)) do
                    K0 := Knext;
                    Knext := RECOG.DerivedSubgroupMonteCarlo(K0,20);
                od;
                S := [1..Int(8*(Log2Int(q)+1))];
                for i in [1..Size(S)] do
                    S[i] := PseudoRandom(K0);
                od;
                containsPPD2K := false;
                containsPPD4K := false;

                for i in S do

                    if RECOG.IsSp4SmallPP2K(tau,q,preparelist) then
                        containsPPD2K := true;
                    fi;

                    if RECOG.IsSp4SmallPP4K(tau,q,preparelist) then
                        containsPPD4K := true;
                    fi;

                od;

                if containsPPD2K and not(containsPPD4K) then
                    return [K0,SLPOfElms(GeneratorsOfGroup(K0))];
                fi;

                counter := counter + 1;
            od;
        fi;
        counter := counter + 1;
    od;

    if counter >= 100 then
        return fail;
    fi;

end;



RECOG.ConstructKOdd := function(G, q)
local count, tau, order, centre, n, taun, K0, K, CentralElement, g;

    count := 0;
    
    #TODO: Don't have do compute this right? Always the same two diagonal matrices
    
    while count < 30 do
        tau := PseudoRandom(G);
        order := Order(tau);
        if (order mod 2 = 0) then
            n := order/2;
            taun := tau^n;
            CentralElement := true;
            for g in GeneratorsOfGroup(G) do
                if g*taun*g^(-1) <> taun then
                    CentralElement := false;
                    break;
                fi;
            od;
            if not(CentralElement) then
                K0 := GroupByGenerators(RECOG.CentraliserOfInvolution(G,taun,[],true,100,RECOG.CompletionCheck,PseudoRandom)[1]);
                K := RECOG.DerivedSubgroupMonteCarlo(K0,20);
                return [K,SLPOfElms(GeneratorsOfGroup(K))];
            fi;
        fi;;
        count := count + 1;
    od;

    return fail;
end;



# Extracting the two factors is done by the methods descibed by Leedham-Green and O'Brien in "Constructive recognition of classical groups in odd characteristic"
# Section 11
# Note that the method for even involutions is not implemented in GAP yet and so there is no method for extracting the two factors in even characteristic
RECOG.ExtractTwoSL2Factors := function(h, q)
local counter, ele, x, x2, ord, invo, found, cent, product, eigenspace, Minuseigenspace, newbasis, dimeigen, dimMinuseigen, r1, r2, result, result2;

    if not(IsObjWithMemory(GeneratorsOfGroup(h)[1])) then
        h := GroupWithMemory(h);
    fi;

    # First we construct an involution i in h

    found := false;
    for counter in [1..100] do
        ele := PseudoRandom(h);
        x := RECOG.EstimateOrder(ele);
        x2 := x[2];
        ord := x[3];
        if x2 <> One(h) then
            invo := x2^(ord/2);
        else
            invo := One(h);
        fi;

        if invo <> One(h) and invo^2 = One(h) then
            eigenspace := Eigenspaces(GF(q),invo);
            if Size(eigenspace) <> 1 then
                Minuseigenspace := eigenspace[2];
                eigenspace := eigenspace[1];
                dimeigen := Dimension(eigenspace);
                dimMinuseigen := Dimension(Minuseigenspace);
                if dimeigen = 2 then
                    found := true;
                    break;
                fi;
            fi;
        fi;
    od;

    if not(found) then
        Error("could not find an involution");
    fi;

    newbasis := MutableCopyMat(BasisVectors(Basis(eigenspace)));
    Append(newbasis,BasisVectors(Basis(Minuseigenspace)));

    if not(Determinant(newbasis) = One(GF(q))) then
        newbasis[4] := Determinant(newbasis)^(-1)*newbasis[4];
    fi;

    # Second we compute the two factors by computing the centralizer of the involution i

    cent := RECOG.CentraliserOfInvolution(h,invo,[],true,100,RECOG.CompletionCheck,PseudoRandom);
    product := GroupByGenerators(cent[1]);

    # Third we continue as in "Constructive recognition of classical groups in odd characteristic" part 11 to find generator

    r1 := [3,4];
    r2 := [1,2];
    for counter in [1..200] do
        result := RECOG.ConstructSmallSub(r1, r2, product, newbasis, g -> RECOG.IsThisSL2Natural(GeneratorsOfGroup(g),GF(q)));
        if result <> fail then
            break;
        fi;
    od;
    if result = fail then
        return fail;
    fi;

    r1 := [1,2];
    r2 := [3,4];
    for counter in [1..200] do
        result2 := RECOG.ConstructSmallSub(r1, r2, product, newbasis, g -> RECOG.IsThisSL2Natural(GeneratorsOfGroup(g),GF(q)));
        if result2 <> fail then
            break;
        fi;
    od;
    if result2 = fail then
        return fail;
    fi;

    return [result[1], result2[1], result[2], result2[2], newbasis];

end;



###################################################################################################
###################################################################################################
######## Test version for Sp(n,2^f) ###############################################################
###################################################################################################
###################################################################################################




RECOG.MakeSp_StdGens := function(p,ext,n,d)
    local a,b,c,f,i,q,s,t,u,x,res,l1,l2;
    f := GF(p,ext);
    q := Size(f);
    l1 := [2..n/2];
    Add(l1,1);
    l2 := [n/2+2..n];
    Add(l2,n/2+1);
    a := PermutationMat(PermList(l1)*MappingPermListList(l2,[(n/2)+1..n]),d,f);
    ConvertToMatrixRep(a,q);
    b := PermutationMat((1,2)(n-1,n),d,GF(q));
    ConvertToMatrixRep(b,q);
    c := PermutationMat((1,n),d,GF(q));
    c[n,1] := -1*One(f);
    ConvertToMatrixRep(c,q);
    s := [];
    t := [];
    u := [];
    for i in [0..ext-1] do
        x := IdentityMat(d,f);
        x[1,2] := Z(p,ext)^i;
        x[n-1,n] := -1*Z(p,ext)^i;
        Add(s,x);
        x := IdentityMat(d,f);
        x[2,1] := Z(p,ext)^i;
        x[n,n-1] := -1*Z(p,ext)^i;
        Add(t,x);
        x := IdentityMat(d,f);
        x[1,n] := Z(p,ext)^i;
        Add(u,x);
    od;
    res := rec( s := s, t := t, u := u, a := a, b := b, c:= c, f := f, q := q, p := p,
                ext := ext, One := IdentityMat(d,f), one := One(f),
                d := d );
    res.all := Concatenation( res.s, res.t, res.u, [res.a], [res.b], [res.c] );
    return res;
end;