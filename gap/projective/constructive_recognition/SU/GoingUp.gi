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
######## GoingUp method for unitary groups ##################################
#############################################################################
#############################################################################



RECOG.SolveNormEquationSilly := function(F,phi,value)
local x;

    for x in Elements(F) do
        if x <> Zero(F) and x*x^phi = value then
            return x;
        fi;
    od;

    return fail;

end;



RECOG.SolveMyBachelorEquationSilly := function(F,phi,value)
local x;

    for x in Elements(F) do
        if x <> Zero(F) and x+x^phi+value*value^phi = Zero(F) then
            return x;
        fi;
    od;

    return fail;

end;



RECOG.BaseChangeToCorrectForm := function(form,n,aimdim,one)
local value, vectors, i, basechange, v1, v2;

    value := (form!.matrix)[1,n];
    vectors := [];
    for i in [n+1 .. aimdim] do
        Add(vectors,one[i]);
    od;

    v1 := vectors[1];
    v2 := Last(vectors);
    Remove(vectors,1);
    Remove(vectors,Position(vectors,v2));
    Error("here");

    return basechange;

end;



RECOG.ComputeCorrectingPermutationMat := function(d,F,n,aimdim)
local list, half, plus, minus, next, current;

    half := n/2;
    plus := aimdim-n;
    minus := aimdim - half;
    list := [half+1];
    current := list[1];
    next := current + plus;
    if next > aimdim then
        next := next - minus;
    fi;
    while not(next in list) do
        Add(list,next);
        current := next;
        next := current + plus;
        if next > aimdim then
            next := next - minus;
        fi;
    od;

    return PermutationMat(CycleFromList(list),d,F);

end;


RECOG.ComputeCorrectingPermutationMatOdd := function(d,F,n,aimdim)
local list, half;

    list := Concatenation([n+1..aimdim],[(n/2)+1..n]);

    return PermutationMat(MappingPermListList([(n/2)+1..aimdim],list)^(-1),d,F);

end;



# change input into H again
RECOG.SUn_UpStep := function(H,G,n,basechange,phi)
# w has components:
#   d       : size of big SL
#   n       : size of small SL
#   slnstdf : fakegens for SL_n standard generators
#   bas     : current base change, first n vectors are where SL_n acts
#             rest of vecs are invariant under SL_n
#   basi    : current inverse of bas
#   sld     : original group with memory generators, PseudoRandom
#             delivers random elements
#   sldf    : fake generators to keep track of what we are doing
#   f       : field
# The following are filled in automatically if not already there:
#   p       : characteristic
#   ext     : q=p^ext
#   One     : One(slnstdf[1])
#   can     : CanonicalBasis(f)
#   canb    : BasisVectors(can)
#   transh  : fakegens for the "horizontal" transvections n,i for 1<=i<=n-1
#             entries can be unbound in which case they are made from slnstdf
#   transv  : fakegens for the "vertical" transvections i,n for 1<=i<=n-1
#             entries can be unbound in which case they are made from slnstdf
#
# We keep the following invariants (going from n -> n':=2n-1)
#   bas, basi is a base change to the target base
#   slnstdf are SLPs to reach standard generators of SL_n from the
#       generators of sld
local d, id, q, p, F, t, GM, counter, aimdim, newdim, c1, c, ci, sum1, int1, i, v1, v2, v3, L1, L2, newpart, zerovec, MB, newbas, newbasi, int3, pivots, cii, pivots2, 
      newbasechange, trans, tf, lambda, killer, transr, gamma1, gamma2, gamma3, gamma4, gamma0, zeta, k, beta, vectorw, normx, PermMat, PermMat2, HBig, HBigGens, H2n, HSmall, transd,
      WrongForm, ChangeToCorrectForm, ChangeToCorrectFormBig, extract, ChangeToCorrectForm2, ChangeToCorrectFormBig2, FormValue, killervalue, killersupport, vectorlist, VC, VCBasis, 
      LinearCombinationVector, s, flag, v, PermMat3, fixv, factors, ext, vectorlistindex, vectorlist2, vectorlistele, indexlist, VCBuildBasis, CanonicalVC;

    F := FieldOfMatrixGroup(H);
    d := Size(GeneratorsOfGroup(G)[1]);
    q := Size(F);
    factors := Factors(q);
    p := factors[1];
    ext := Size(factors);

    # Here everything starts, some more preparations:

    # We compute exclusively in our basis, so we occasionally need an
    # identity matrix:
    id := IdentityMat(d,F);

    Info(InfoRecog,2,"Current dimension: " );
    Info(InfoRecog,2,n);
    Info(InfoRecog,2,"\n");
    Info(InfoRecog,2,"New dimension: ");
    Info(InfoRecog,2,Minimum(2*n-2,d));
    Info(InfoRecog,2,"\n");
    aimdim := Minimum(2*n-2,d);
    newdim := aimdim - n;
    counter := 0;

    Info(InfoRecog,2,"Preparation done.");

    # Generalise the next step
    t := IdentityMat(d,F);
    if n = 4 then
        t[1,2] := One(F);
        t[3,4] := -1*One(F);
        t[1,4] := PrimitiveElement(F)^3;
    fi;

    if n = 6 then
        t[1,2] := One(F);
        t[1,3] := One(F);
        t[2,3] := One(F);
        t[4,5] := -1*One(F);
        t[5,6] := -1*One(F);
        t := PermutationMat((1,2,3)(6,5,4),d,F);
    fi;

    if n > 6 then 
        v := Zero(F) * IdentityMat( n, F );
        v[n/2][1] := One(F);
        v{[1..(n/2)-1]}{[2..n/2]} := IdentityMat((n/2)-1,F);
        v[n/2+1][n] := One(F);
        v{[(n/2)+2..n]}{[(n/2)+1..n-1]} := IdentityMat((n/2)-1,F);
        t{[1..n]}{[1..n]} := v;
        #Display(t);
        #Display(t^basechange in G);
    fi;

    Info(InfoRecog,2,"Step 1 done.");

    # Find a good random element:
    while true do   # will be left by break
        while true do    # will be left by break
            counter := counter + 1;
            if InfoLevel(InfoRecog) >= 3 then Print(".\c"); fi;
            c1 := PseudoRandom(G);
            
            # Do the base change into our basis:
            c1 := c1^(basechange^(-1));
            c := t^c1;
            
            # Now check that Vn + Vn*s^c1 has dimension 2n-1:
            sum1 := SumIntersectionMat(c{[1..n]},id{[1..n]});
   
            if Size(sum1[1]) = aimdim then

                int1 := SumIntersectionMat(RECOG.FixspaceMat(c),id{[1..n]})[2];

                for i in [1..Size(int1)] do
                    v1 := int1[i];
                    if not(IsZero(v1[1])) then break; fi;
                od;
                for i in [1..Size(int1)] do
                    v2 := int1[i];
                    if (v1 <> v2) and not(IsZero(v2[n])) then break; fi;
                od;
                if (v1 = v2) or IsZero(v1[1]) or IsZero(v2[n]) then
                    Info(InfoRecog,2,"Ooops: Component n was zero!");
                    continue;
                fi;

                v1 := v1 / v1[1];   # normalize to 1 in position 1
                Assert(1,v1*c=v1);

                v2 := v2 / v2[n];   # normalize to 1 in position n
                Assert(1,v2*c=v2);

                v1 := v1 + (-1) * v1[n] * v2;
                v2 := v2 + (-1) * v2[1] * v1;

                # Actually we don't need gamma3 here
                gamma1 := Zero(F);
                gamma2 := One(F);
                gamma3 := One(F);
                gamma4 := Zero(F);
                for k in [2..n-1] do
                    gamma1 := gamma1 + v2[k]*(v2[n-k+1])^phi;
                od;

                if gamma1 = Zero(F) then
                    Info(InfoRecog,2,"Ooops: gamma1 was zero!");
                    continue;
                fi;

                for k in [2..n-1] do
                    gamma4 := gamma4 + v1[k]*(v1[n-k+1])^phi;
                od;
                for k in [2..n-1] do
                    gamma2 := gamma2 + v2[k]*(v1[n-k+1])^phi;
                od;
                for k in [2..n-1] do
                    gamma3 := gamma3 + v1[k]*(v2[n-k+1])^phi;
                od;

                gamma0 := RECOG.SolveNormEquationSilly(F,phi,gamma1);
                zeta := gamma2*gamma0^(-1);
                normx := RECOG.SolveNormEquationSilly(F,phi,zeta*zeta^phi-gamma4);

                if zeta*zeta^phi-gamma4 = Zero(F) then
                    Info(InfoRecog,2,"Ooops: zeta*zeta^phi-gamma4 was zero!");
                    continue;
                fi;

                beta := (normx-zeta^phi)*gamma0^(-1);

                vectorw := v1 + beta * v2;

                L1 := IdentityMat(d,F);
                for i in [2..n-1] do
                    L1[1,i] := vectorw[i];
                    L1[n-i+1,n] := -1*vectorw[i]^phi;
                od;
                L1[1,n] := beta;

                if not(L1^basechange in G) then
                    Info(InfoRecog,2,"Ooops: Component not useable!");
                    Print("foul play");
                    Error("here");
                    continue;
                fi;

                c := L1*c*L1^(-1);
                int1 := SumIntersectionMat(RECOG.FixspaceMat(c),id{[1..n]})[2];
                for i in [1..Size(int1)] do
                    v2 := int1[i];
                    if not(IsZero(v2[n])) then break; fi;
                od;

                if IsZero(v2[n]) then
                    Info(InfoRecog,2,"Ooops: Component n was zero!");
                    continue;
                fi;

                v1 := id[1];
                v2 := v2 / v2[n];   # normalize to 1 in position n
                Assert(1,v2*c=v2);

                v2 := v2 + (-1) * v2[1] * v1;

                gamma1 := Zero(F);
                for k in [2..n-1] do
                    gamma1 := gamma1 + v2[k]*(v2[n-k+1])^phi;
                od;
                normx := RECOG.SolveNormEquationSilly(F,phi,gamma1);
                beta := RECOG.SolveMyBachelorEquationSilly(F,phi,normx);

                vectorw := v2 + beta * v1;

                L2 := IdentityMat(d,F);
                for i in [2..n-1] do
                    L2[n,i] := vectorw[i];
                    L2[n-i+1,1] := -1*vectorw[i]^phi;
                od;
                L2[n,1] := beta;

                if not(L2^basechange in G) then
                    Info(InfoRecog,2,"Ooops: Component not useable!");
                    Print("foul play");
                    Error("here");
                    continue;
                fi;

                c := L2*c*L2^(-1);
                ci := c^-1;
                break;
            fi;
            # Display(counter);
        od;
        
        Info(InfoRecog,2,"Step 2 done.");

        # Now we found our aimdim-dimensional space W. Since SL_n
        # has a d-n-dimensional fixed space W_{d-n} and W contains a complement
        # of that fixed space, the intersection of W and W_{d-n} has dimension
        # newdim.

        # Change basis:
        newpart := ExtractSubMatrix(c,[2..(n-1)],[1..(d)]);
        # Clean out the first n entries to go to the fixed space of SL_n:
        zerovec := Zero(newpart[1]);
        for i in [1..(n-2)] do
            CopySubVector(zerovec,newpart[i],[1..n],[1..n]);
        od;
        MB := MutableBasis(F,[],zerovec);
        i := 1;
        pivots := EmptyPlist(newdim);
        while i <= Length(newpart) and NrBasisVectors(MB) < newdim do
            if not(IsContainedInSpan(MB,newpart[i])) then
                Add(pivots,i);
                CloseMutableBasis(MB,newpart[i]);
            fi;
            i := i + 1;
        od;

        newpart := newpart{pivots};
        newbas := Concatenation(id{[1..n]},newpart);
        if 2*n-2 < d then

            int3 := SumIntersectionMat(RECOG.FixspaceMat(c),id{[n+1..d]})[2];
            
            if Size(int3) <> d - aimdim then
                Info(InfoRecog,2,"Ooops, FixSLn \cap Fixc wrong dimension");
                #Error("neues beispiel");
                continue;
            fi;
            Append(newbas,int3);

        fi;
        ConvertToMatrixRep(newbas,Size(F));
        newbasi := newbas^-1;
        if newbasi = fail then
            Info(InfoRecog,2,"Ooops, Fixc intersected too much, we try again");
            continue;
        fi;
        
        ci := newbas * ci * newbasi;

        cii := ExtractSubMatrix(ci,[n+1..aimdim],[2..n-1]);
        ConvertToMatrixRep(cii,Size(F));
        cii := TransposedMat(cii);
        # The rows of cii are now what used to be the columns,
        # their length is newdim, we need to span the full newdim-dimensional
        # row space and need to remember how:
        zerovec := Zero(cii[1]);
        MB := MutableBasis(F,[],zerovec);
        i := 1;
        pivots2 := EmptyPlist(newdim);
        while i <= Length(cii) and NrBasisVectors(MB) < newdim do
            if not(IsContainedInSpan(MB,cii[i])) then
                Add(pivots2,i);
                CloseMutableBasis(MB,cii[i]);
            fi;
            i := i + 1;
        od;
        if Length(pivots2) = newdim then
            cii := cii{pivots2}^-1;
            ConvertToMatrixRep(cii,F);

            c := newbas * c * newbasi;
            newbasechange := newbas*basechange;
            break;
        fi;
        Info(InfoRecog,2,"Ooops, no nice bottom...");
        # Otherwise simply try again
    od;

    HBigGens := List(GeneratorsOfGroup(H),MutableCopyMat);
    Append(HBigGens,GeneratorsOfGroup(H^c));
    HBig := GroupByGenerators(HBigGens);
    basechange := newbasechange;
    #Display(RecogniseClassical(RECOG.LinearActionRepresentation(HBig)));
    HSmall := GroupByGenerators(List(GeneratorsOfGroup(HBig),x->x{[1..aimdim]}{[1..aimdim]}));
    WrongForm := PreservedSesquilinearForms(HSmall)[1];
    extract := HermitianFormByMatrix((WrongForm!.matrix){[n+1..aimdim]}{[n+1..aimdim]}, F );
    FormValue := (WrongForm!.matrix)[1,n];
    ChangeToCorrectForm := BaseChangeToCanonical(extract);
    ChangeToCorrectFormBig := IdentityMat(aimdim,F);
    ChangeToCorrectFormBig{[n+1..aimdim]}{[n+1..aimdim]} := ChangeToCorrectForm;

    PermMat := One(SymmetricGroup(aimdim));
    if IsEvenInt(aimdim) then
        for i in [1..(n/2)] do
            PermMat := PermMat*(i,n-i+1);
        od;
        for i in [n+1..(n+aimdim)/2] do
            PermMat := PermMat*(i,aimdim-i+n+1);
        od;
        PermMat := PermutationMat(PermMat,d,F);
        PermMat2 := One(SymmetricGroup(aimdim));
        for i in [1..aimdim/2] do
            PermMat2 := PermMat2*(i,aimdim-i+1);
        od;
        PermMat2 := PermutationMat(PermMat2,d,F);
    else
        for i in [1..(n/2)] do
            PermMat := PermMat*(i,n-i+1);
        od;
        for i in [n+1..(n-1+aimdim)/2] do
            PermMat := PermMat*(i,aimdim-i+n+1);
        od;
        PermMat := PermutationMat(PermMat,d,F);
        PermMat2 := One(SymmetricGroup(aimdim));
        for i in [1..(aimdim-1)/2] do
            PermMat2 := PermMat2*(i,aimdim-i+1);
        od;
        PermMat2 := PermutationMat(PermMat2,d,F);
    fi;

    WrongForm := IdentityMat(aimdim,F);
    WrongForm{[n+1..aimdim]}{[n+1..aimdim]} := FormValue*PermMat{[n+1..aimdim]}{[n+1..aimdim]};
    ChangeToCorrectForm2 := BaseChangeToCanonical(HermitianFormByMatrix(WrongForm, F ));
    ChangeToCorrectFormBig2 := IdentityMat(d,F);
    ChangeToCorrectFormBig2{[1..aimdim]}{[1..aimdim]} := ChangeToCorrectFormBig^(-1)*ChangeToCorrectForm2;
    HBig := HBig^ChangeToCorrectFormBig2;
    basechange := ChangeToCorrectFormBig2^(-1)*basechange;

    while true do   # will be left by break
        while true do    # will be left by break
            counter := counter + 1;
            if InfoLevel(InfoRecog) >= 3 then Print(".\c"); fi;

            c1 := PseudoRandom(HBig);
            c := t^c1;

            # Now check that Vn + Vn*s^c1 has dimension 2n-2:
            sum1 := SumIntersectionMat(c{[1..n]},id{[1..n]});
            
            if Size(sum1[1]) = aimdim then
       
                int1 := SumIntersectionMat(RECOG.FixspaceMat(c),id{[1..n]})[2];

                for i in [1..Size(int1)] do
                    v1 := int1[i];
                    if not(IsZero(v1[1])) then break; fi;
                od;
                for i in [1..Size(int1)] do
                    v2 := int1[i];
                    if (v1 <> v2) and not(IsZero(v2[n])) then break; fi;
                od;
                if (v1 = v2) or IsZero(v1[1]) or IsZero(v2[n]) then
                    Info(InfoRecog,2,"Ooops: Component n was zero!");
                    continue;
                fi;

                v1 := v1 / v1[1];   # normalize to 1 in position 1
                Assert(1,v1*c=v1);

                v2 := v2 / v2[n];   # normalize to 1 in position n
                Assert(1,v2*c=v2);

                v1 := v1 + (-1) * v1[n] * v2;
                v2 := v2 + (-1) * v2[1] * v1;

                # Actually we don't need gamma3 here
                gamma1 := Zero(F);
                gamma2 := One(F);
                gamma3 := One(F);
                gamma4 := Zero(F);
                for k in [2..n-1] do
                    gamma1 := gamma1 + v2[k]*(v2[n-k+1])^phi;
                od;

                if gamma1 = Zero(F) then
                    Info(InfoRecog,2,"Ooops: gamma1 was zero!");
                    continue;
                fi;

                for k in [2..n-1] do
                    gamma4 := gamma4 + v1[k]*(v1[n-k+1])^phi;
                od;
                for k in [2..n-1] do
                    gamma2 := gamma2 + v2[k]*(v1[n-k+1])^phi;
                od;
                for k in [2..n-1] do
                    gamma3 := gamma3 + v1[k]*(v2[n-k+1])^phi;
                od;

                gamma0 := RECOG.SolveNormEquationSilly(F,phi,gamma1);
                zeta := gamma2*gamma0^(-1);
                normx := RECOG.SolveNormEquationSilly(F,phi,zeta*zeta^phi-gamma4);

                if zeta*zeta^phi-gamma4 = Zero(F) then
                    Info(InfoRecog,2,"Ooops: zeta*zeta^phi-gamma4 was zero!");
                    continue;
                fi;

                beta := (normx-zeta^phi)*gamma0^(-1);

                vectorw := v1 + beta * v2;

                L1 := IdentityMat(d,F);
                for i in [2..n-1] do
                    L1[1,i] := vectorw[i];
                    L1[n-i+1,n] := -1*vectorw[i]^phi;
                od;
                L1[1,n] := beta;

                if not(L1^basechange in G) then
                    Info(InfoRecog,2,"Ooops: Component not useable!");
                    Print("foul play");
                    Error("here");
                    continue;
                fi;

                c := L1*c*L1^(-1);
                int1 := SumIntersectionMat(RECOG.FixspaceMat(c),id{[1..n]})[2];
                for i in [1..Size(int1)] do
                    v2 := int1[i];
                    if not(IsZero(v2[n])) then break; fi;
                od;

                if IsZero(v2[n]) then
                    Info(InfoRecog,2,"Ooops: Component n was zero!");
                    continue;
                fi;

                v1 := id[1];
                v2 := v2 / v2[n];   # normalize to 1 in position n
                Assert(1,v2*c=v2);

                v2 := v2 + (-1) * v2[1] * v1;

                gamma1 := Zero(F);
                for k in [2..n-1] do
                    gamma1 := gamma1 + v2[k]*(v2[n-k+1])^phi;
                od;
                normx := RECOG.SolveNormEquationSilly(F,phi,gamma1);
                beta := RECOG.SolveMyBachelorEquationSilly(F,phi,normx);

                vectorw := v2 + beta * v1;

                L2 := IdentityMat(d,F);
                for i in [2..n-1] do
                    L2[n,i] := vectorw[i];
                    L2[n-i+1,1] := -1*vectorw[i]^phi;
                od;
                L2[n,1] := beta;

                if not(L2^basechange in G) then
                    Info(InfoRecog,2,"Ooops: Component not useable!");
                    Print("foul play");
                    Error("here");
                    continue;
                fi;

                c := L2*c*L2^(-1);
                ci := c^-1;
                break;
            fi;
        od;
        
        Info(InfoRecog,2,"Step 2 done.");

        break;
    od;

    Info(InfoRecog,2," found c1 and c.");

    Info(InfoRecog,2,"Step 3 and 4 done");

    # Now consider the transvections t_i:
    # t_i : w.bas[j] -> w.bas[j]        for j <> i and
    # t_i : w.bas[i] -> w.bas[i] + ww
    # We want to modify (t_i)^c such that it fixes w.bas{[1..w.n]}:
    if not(IsEvenInt(aimdim)) then
        trans := [];
        vectorlist := [];
        for i in [1..(n-2)] do
            # This does t_i
            for lambda in [One(F),PrimitiveElement(GF(25))] do
                # This does t_i : v_j -> v_j + lambda * v_n
                tf := IdentityMat(d,F);
                tf[i+1,n] := lambda;
                tf[1,n-i] := -1*(lambda^phi);
                # Now conjugate with c:
                tf := ci*tf*c;
                # Now cleanup in column n above row n, the entries there
                # are lambda times the stuff in column i of ci:
                #for j in [1..w.n-1] do
                #    tf := DoRowOp_n(tf,j,w.n,-ci[j,i]*lambda,w);
                #od;
                killer := IdentityMat(d,F);
                for killervalue in [2..n-1] do
                    killersupport := IdentityMat(d,F);
                    killersupport[1,killervalue] := (-1)*tf[1,killervalue];
                    killersupport[n-killervalue+1,n] := (tf[1,killervalue])^phi;
                    #Display(killersupport);
                    killer := killer*killersupport;
                od;
                #killer{[1..n]}{[1..n]} := tf{[1..n]}{[1..n]}^(-1);
                if killer^newbasechange in G then
                    tf := killer*tf;
                else
                    Error("this should not happen.");
                fi;
                Add(vectorlist,tf{[n+1..aimdim]}{[n]});
                Add(trans,tf);
            od;
        od;

        # For now vector space variant. but change that!
        VC := VectorSpace(GF(p),vectorlist);

        # If we are finishing up, then we have to take a linear independent subset
        if aimdim < 2*n-2 then
            vectorlist2 := [];
            indexlist := [];
            for vectorlistindex in [1..Size(vectorlist)] do
                vectorlistele := vectorlist[vectorlistindex];
                VCBuildBasis:=VectorSpace( GF(p), Concatenation(vectorlist2,[vectorlistele]) );
                if Dimension(VCBuildBasis) > Length(vectorlist2) then
                    Add(vectorlist2,vectorlistele);
                    Add(indexlist,vectorlistindex);
                fi;
                if Length(vectorlist2) = Dimension(VC) then
                    break;
                fi;
            od;
            VCBasis := Basis(VC,vectorlist2);
        else
            VCBasis := Basis(VC,vectorlist);
        fi;

        # # Now put together the clean ones by our knowledge of c^-1:
        transd := [];
        CanonicalVC := BasisVectors(CanonicalBasis(VC));
        for i in CanonicalVC do
            LinearCombinationVector := Coefficients(VCBasis,i);
            tf := IdentityMat(d,F);

            # TODO: We need to take the substitute trans[lambda] by trans[indexlist[lambda]] or something like that
            for lambda in [1..Size(LinearCombinationVector)] do
                tf := tf*trans[lambda]^Int(LinearCombinationVector[lambda]);
            od;
            killer{[1..n]}{[1..n]} := tf{[1..n]}{[1..n]}^(-1);
            if not(Position(CanonicalVC,i) in [Size(CanonicalVC)/2,Size(CanonicalVC)/2 + 1]) then
                if killer^newbasechange in G then
                    tf := killer*tf;
                else
                    Error("this should not happen.");
                fi;
            fi;
            Add(transd,tf);
        od;
        Unbind(trans);

        Info(InfoRecog,2,"Step 5 done");

        # Now to the "horizontal" transvections, first create them as SLPs:
        transr := [];
        trans := [];
        vectorlist := [];
        for lambda in [One(F),PrimitiveElement(GF(25))] do
            # This does t_i
            for i in [2..(n-1)] do
                # This does t_i : v_j -> v_j + lambda * v_n
                tf := IdentityMat(d,F);
                tf[i,1] := lambda;
                tf[n,n-i+1] := -1*(lambda^phi);
                # Now conjugate with c:
                tf := ci*tf*c;
                # Now cleanup in column n above row n, the entries there
                # are lambda times the stuff in column i of ci:
                #for j in [1..w.n-1] do
                #    tf := DoRowOp_n(tf,j,w.n,-ci[j,i]*lambda,w);
                #od;
                killer := IdentityMat(d,F);
                for killervalue in [2..n-1] do
                    killersupport := IdentityMat(d,F);
                    killersupport[killervalue,1] := (-1)*tf[killervalue,1];
                    killersupport[n,n-killervalue+1] := (tf[killervalue,1])^phi;
                    #Display(killersupport);
                    killer := killer*killersupport;
                od;
                #killer{[1..n]}{[1..n]} := tf{[1..n]}{[1..n]}^(-1);
                if killer^newbasechange in G then
                    tf := killer*tf;
                else
                    Error("this should not happen.");
                fi;
                Add(vectorlist,tf{[n]}{[n+1..aimdim]});
                Add(trans,tf);
            od;
        od;

        # For now vector space variant. but change that!
        VC := VectorSpace(GF(p),vectorlist);
        if aimdim < 2*n-2 then
            vectorlist2 := [];
            indexlist := [];
            for vectorlistindex in [1..Size(vectorlist)] do
                vectorlistele := vectorlist[vectorlistindex];
                VCBuildBasis:=VectorSpace( GF(p), Concatenation(vectorlist2,[vectorlistele]) );
                if Dimension(VCBuildBasis) > Length(vectorlist2) then
                    Add(vectorlist2,vectorlistele);
                    Add(indexlist,vectorlistindex);
                fi;
                if Length(vectorlist2) = Dimension(VC) then
                    break;
                fi;
            od;
            VCBasis := Basis(VC,vectorlist2);
        else
            VCBasis := Basis(VC,vectorlist);
        fi;

        CanonicalVC := BasisVectors(CanonicalBasis(VectorSpace(F,IdentityMat(aimdim-n,F))));
        for i in CanonicalVC do
            LinearCombinationVector := Coefficients(VCBasis,[i]);
            tf := IdentityMat(d,F);
            for lambda in [1..Size(LinearCombinationVector)] do
                tf := tf*trans[indexlist[lambda]]^Int(LinearCombinationVector[lambda]);
            od;
            killer{[1..n]}{[1..n]} := tf{[1..n]}{[1..n]}^(-1);
            if not(Position(CanonicalVC,i) = (Size(CanonicalVC)+1)/2) then
                if killer^newbasechange in G then
                    tf := killer*tf;
                else
                    Error("this should not happen.");
                fi;
            fi;
            Add(transr,tf);
        od;
        Unbind(trans);

        Info(InfoRecog,2,"Step 6 done");

        # From here on we distinguish three cases:
        #   * w.n = 2
        #   * we finish off the constructive recognition
        #   * we have to do another step as the next thing
        if n = 4 then
            #w.slnstdf[2*w.ext+2] := transd[1]*transr[1]^-1*transd[1];
            #w.slnstdf[2*w.ext+1] := w.transh[1]*w.transv[1]^-1*w.transh[1]
            #                        *w.slnstdf[2*w.ext+2];
            #Unbind(w.transh);
            #Unbind(w.transv);
            #w.n := 3;
            flag := false;
            s := IdentityMat(d,F);
            PermMat3 := PermutationMat((3,5)(6,4),d,F);
            v := PermutationMat((1,2)(3,4),d,F);
            #PermMat3 := PermutationMat((3,5)(6,4),20,GF(5));
            # w.ext = 2?
            #for i in [n-1,n-3..1] do
            flag := false;
            for i in [2] do
                if flag then
                    # Make [[0,-1],[1,0]] in coordinates w.n and w.n+i:
                    tf := transd[(i-1)*ext+1]*transr[i]^-1*transd[(i-1)*ext+1];
                else
                    # Make [[0,1],[-1,0]] in coordinates w.n and w.n+i:
                    #Display(transd[(i-1)*1+1]*transr[i]^-1*transd[(i-1)*1+1]);
                    tf := transd[(i-1)*ext+1]^-1*transr[i]*transd[(i-1)*ext+1]^-1;
                fi;
                #Display(tf);
                #Display((tf^(v^2))^(PermMat3^(-1)));
                s := s * tf;
                flag := not(flag);
            od;

            fixv := IdentityMat(d,F);
            fixv[1,1] := -1*One(F);
            fixv[4,4] := -1*One(F);
            newbasechange := PermMat3^(-1)*basechange;
            #Display((v*s*fixv)^(PermMat3^(-1)));
            # Now compute v*s
            Info(InfoRecog,2,"Step 7 done");
            Error("here");
            #return w;
        fi;
        # We can finish off:
        # if aimdim = w.GoalDim then
        #     # In this case we just finish off and do not bother with
        #     # the transvections, we will only need the standard gens:
        #     # Now put together the (newdim+1)-cycle:
        #     # n+newdim -> n+newdim-1 -> ... -> n+1 -> n -> n+newdim
        #     flag := false;
        #     s := w.One;
        #     for i in [1..newdim] do
        #         if flag then
        #             # Make [[0,-1],[1,0]] in coordinates w.n and w.n+i:
        #             tf:=transd[(i-1)*w.ext+1]*transr[i]^-1*transd[(i-1)*w.ext+1];
        #         else
        #             # Make [[0,1],[-1,0]] in coordinates w.n and w.n+i:
        #             tf:=transd[(i-1)*w.ext+1]^-1*transr[i]*transd[(i-1)*w.ext+1]^-1;
        #         fi;
        #         s := s * tf;
        #         flag := not(flag);
        #     od;

        #     # Finally put together the new 2n-1-cycle and 2n-2-cycle:
        #     s := s^-1;
        #     w.slnstdf[2*w.ext+1] := w.slnstdf[2*w.ext+1] * s;
        #     w.slnstdf[2*w.ext+2] := w.slnstdf[2*w.ext+2] * s;
        #     Unbind(w.transv);
        #     Unbind(w.transh);
        #     w.n := aimdim;
        #     Display("Step 7 done");
        #     return w;
        # fi;

        # Otherwise we do want to go on as the next thing, so we want to
        # keep our transvections. This is easily done if we change the
        # basis one more time. Note that we know that n is odd here!

        # Put together the n-cycle:
        # 2n-1 -> 2n-2 -> ... -> n+1 -> n -> 2n-1

        # TODO: WE HAVE TO COMBINE THE v-CYCLE DIFFERENTLY HERE

        flag := false;
        s := IdentityMat(d,F);
        #PermMat3 := PermutationMat((4,7,10,6,9,5,8),20,GF(5));
        PermMat3 := RECOG.ComputeCorrectingPermutationMatOdd(d,F,n,aimdim);
        Display(PermMat3);

        # TODO: Last step of building v in odd dimension
        Error("here");
        v := Zero(F) * IdentityMat( d, F );
        v[n/2][1] := One(F);
        v{[1..(n/2)-1]}{[2..n/2]} := IdentityMat((n/2)-1,F);
        v[n/2+1][n] := One(F);
        v{[(n/2)+2..n]}{[(n/2)+1..n-1]} := IdentityMat((n/2)-1,F);
        v{[n+1..d]}{[n+1..d]} := IdentityMat(d-n,F);
        #Display(t);
        #Display(t^basechange in G);
        #PermMat3 := PermutationMat((3,5)(6,4),20,GF(5));
        # w.ext = 2?
        #for i in [n-1,n-3..1] do
        #for i in [Size(transr)-1,Size(transr)-3..5] do
        for i in [n-2,n-3..(n/2)] do
            if flag then
                # Make [[0,-1],[1,0]] in coordinates w.n and w.n+i:
                # TODO: Replace 2 by size of extension to get the correct matrices of transd (we want the ones with 1 and -1 at the transvection positions)
                tf := transd[(i-1)*ext+1]*transr[i]^-1*transd[(i-1)*ext+1];
            else
                # Make [[0,1],[-1,0]] in coordinates w.n and w.n+i:
                # TODO: Replace 2 by size of extension to get the correct matrices of transd (we want the ones with 1 and -1 at the transvection positions)
                tf := transd[(i-1)*ext+1]^-1*transr[i]*transd[(i-1)*ext+1]^-1;
            fi;
            #Display(tf);
            #Display((tf^(v^2))^(PermMat3^(-1)));
            #Display(tf);
            s := s * tf;
            flag := not(flag);
        od;

        #Display(((v*s)^(-1))^(PermMat3));
        newbasechange := PermMat3^(-1)*basechange;
        # Now compute v*s
        # Info(InfoRecog,2,"Step 7 done");
        Error("here");

        # # Finally put together the new 2n-1-cycle and 2n-2-cycle:
        # w.slnstdf[2*w.ext+1] := s * w.slnstdf[2*w.ext+1];
        # w.slnstdf[2*w.ext+2] := s * w.slnstdf[2*w.ext+2];

        # list := Concatenation([1..w.n-1],[w.n+1..2*w.n-1],[w.n],[2*w.n..w.d]);
        # perm := PermList(list);
        # mat := PermutationMat(perm^-1,w.d,w.f);
        # ConvertToMatrixRep(mat,w.f);
        # w.bas := w.bas{list};
        # ConvertToMatrixRep(w.bas,w.f);
        # w.basi := w.basi*mat;

        # # Now add the new transvections:
        # for i in [1..w.n-1] do
        #     w.transh[w.ext*(w.n-1)+w.ext*(i-1)+1] := transr[i];
        # od;
        # Append(w.transv,transd);
        # w.n := 2*w.n-1;

        #if( aimdim = 5) then
        #  Error("here");
        #fi;
    else
        trans := [];
        vectorlist := [];
        for i in [1..(n-2)] do
            # This does t_i
            for lambda in [One(F),PrimitiveElement(GF(25))] do
                # This does t_i : v_j -> v_j + lambda * v_n
                tf := IdentityMat(d,F);
                tf[i+1,n] := lambda;
                tf[1,n-i] := -1*(lambda^phi);
                # Now conjugate with c:
                tf := ci*tf*c;
                # Now cleanup in column n above row n, the entries there
                # are lambda times the stuff in column i of ci:
                #for j in [1..w.n-1] do
                #    tf := DoRowOp_n(tf,j,w.n,-ci[j,i]*lambda,w);
                #od;
                killer := IdentityMat(d,F);
                for killervalue in [2..n-1] do
                    killersupport := IdentityMat(d,F);
                    killersupport[1,killervalue] := (-1)*tf[1,killervalue];
                    killersupport[n-killervalue+1,n] := (tf[1,killervalue])^phi;
                    #Display(killersupport);
                    killer := killer*killersupport;
                od;
                #killer{[1..n]}{[1..n]} := tf{[1..n]}{[1..n]}^(-1);
                if killer^newbasechange in G then
                    tf := killer*tf;
                else
                    Error("this should not happen.");
                fi;
                Add(vectorlist,tf{[n+1..aimdim]}{[n]});
                Add(trans,tf);
            od;
        od;

        # For now vector space variant. but change that!
        VC := VectorSpace(GF(p),vectorlist);

        # If we are finishing up, then we have to take a linear independent subset
        if aimdim < 2*n-2 then
            vectorlist2 := [];
            indexlist := [];
            for vectorlistindex in [1..Size(vectorlist)] do
                vectorlistele := vectorlist[vectorlistindex];
                VCBuildBasis:=VectorSpace( GF(p), Concatenation(vectorlist2,[vectorlistele]) );
                if Dimension(VCBuildBasis) > Length(vectorlist2) then
                    Add(vectorlist2,vectorlistele);
                    Add(indexlist,vectorlistindex);
                fi;
                if Length(vectorlist2) = Dimension(VC) then
                    break;
                fi;
            od;
            VCBasis := Basis(VC,vectorlist2);
        else
            VCBasis := Basis(VC,vectorlist);
        fi;

        # # Now put together the clean ones by our knowledge of c^-1:
        transd := [];
        for i in BasisVectors(CanonicalBasis(VC)) do
            LinearCombinationVector := Coefficients(VCBasis,i);
            tf := IdentityMat(d,F);

            # TODO: We need to take the substitute trans[lambda] by trans[indexlist[lambda]] or something like that
            for lambda in [1..Size(LinearCombinationVector)] do
                tf := tf*trans[lambda]^Int(LinearCombinationVector[lambda]);
            od;
            killer{[1..n]}{[1..n]} := tf{[1..n]}{[1..n]}^(-1);
            if killer^newbasechange in G then
                tf := killer*tf;
            else
                Error("this should not happen.");
            fi;
            Add(transd,tf);
        od;
        Unbind(trans);

        Info(InfoRecog,2,"Step 5 done");

        # Now to the "horizontal" transvections, first create them as SLPs:
        transr := [];
        trans := [];
        vectorlist := [];
        for lambda in [One(F),PrimitiveElement(GF(25))] do
            # This does t_i
            for i in [2..(n-1)] do
                # This does t_i : v_j -> v_j + lambda * v_n
                tf := IdentityMat(d,F);
                tf[i,1] := lambda;
                tf[n,n-i+1] := -1*(lambda^phi);
                # Now conjugate with c:
                tf := ci*tf*c;
                # Now cleanup in column n above row n, the entries there
                # are lambda times the stuff in column i of ci:
                #for j in [1..w.n-1] do
                #    tf := DoRowOp_n(tf,j,w.n,-ci[j,i]*lambda,w);
                #od;
                killer := IdentityMat(d,F);
                for killervalue in [2..n-1] do
                    killersupport := IdentityMat(d,F);
                    killersupport[killervalue,1] := (-1)*tf[killervalue,1];
                    killersupport[n,n-killervalue+1] := (tf[killervalue,1])^phi;
                    #Display(killersupport);
                    killer := killer*killersupport;
                od;
                #killer{[1..n]}{[1..n]} := tf{[1..n]}{[1..n]}^(-1);
                if killer^newbasechange in G then
                    tf := killer*tf;
                else
                    Error("this should not happen.");
                fi;
                Add(vectorlist,tf{[n]}{[n+1..aimdim]});
                Add(trans,tf);
            od;
        od;

        # For now vector space variant. but change that!
        VC := VectorSpace(GF(p),vectorlist);
        VCBasis := Basis(VC,vectorlist);

        for i in BasisVectors(CanonicalBasis(VectorSpace(F,IdentityMat(n-2,F)))) do
            LinearCombinationVector := Coefficients(VCBasis,[i]);
            tf := IdentityMat(d,F);
            for lambda in [1..Size(LinearCombinationVector)] do
                tf := tf*trans[lambda]^Int(LinearCombinationVector[lambda]);
            od;
            killer{[1..n]}{[1..n]} := tf{[1..n]}{[1..n]}^(-1);
            if killer^newbasechange in G then
                tf := killer*tf;
            else
                Error("this should not happen.");
            fi;
            Add(transr,tf);
        od;
        Unbind(trans);

        Info(InfoRecog,2,"Step 6 done");

        # From here on we distinguish three cases:
        #   * w.n = 2
        #   * we finish off the constructive recognition
        #   * we have to do another step as the next thing
        if n = 4 then
            #w.slnstdf[2*w.ext+2] := transd[1]*transr[1]^-1*transd[1];
            #w.slnstdf[2*w.ext+1] := w.transh[1]*w.transv[1]^-1*w.transh[1]
            #                        *w.slnstdf[2*w.ext+2];
            #Unbind(w.transh);
            #Unbind(w.transv);
            #w.n := 3;
            flag := false;
            s := IdentityMat(d,F);
            PermMat3 := PermutationMat((3,5)(6,4),d,F);
            v := PermutationMat((1,2)(3,4),d,F);
            #PermMat3 := PermutationMat((3,5)(6,4),20,GF(5));
            # w.ext = 2?
            #for i in [n-1,n-3..1] do
            flag := false;
            for i in [2] do
                if flag then
                    # Make [[0,-1],[1,0]] in coordinates w.n and w.n+i:
                    tf := transd[(i-1)*ext+1]*transr[i]^-1*transd[(i-1)*ext+1];
                else
                    # Make [[0,1],[-1,0]] in coordinates w.n and w.n+i:
                    #Display(transd[(i-1)*1+1]*transr[i]^-1*transd[(i-1)*1+1]);
                    tf := transd[(i-1)*ext+1]^-1*transr[i]*transd[(i-1)*ext+1]^-1;
                fi;
                #Display(tf);
                #Display((tf^(v^2))^(PermMat3^(-1)));
                s := s * tf;
                flag := not(flag);
            od;

            fixv := IdentityMat(d,F);
            fixv[1,1] := -1*One(F);
            fixv[4,4] := -1*One(F);
            newbasechange := PermMat3^(-1)*basechange;
            #Display((v*s*fixv)^(PermMat3^(-1)));
            # Now compute v*s
            Info(InfoRecog,2,"Step 7 done");
            Error("here");
            #return w;
        fi;
        # We can finish off:
        # if aimdim = w.GoalDim then
        #     # In this case we just finish off and do not bother with
        #     # the transvections, we will only need the standard gens:
        #     # Now put together the (newdim+1)-cycle:
        #     # n+newdim -> n+newdim-1 -> ... -> n+1 -> n -> n+newdim
        #     flag := false;
        #     s := w.One;
        #     for i in [1..newdim] do
        #         if flag then
        #             # Make [[0,-1],[1,0]] in coordinates w.n and w.n+i:
        #             tf:=transd[(i-1)*w.ext+1]*transr[i]^-1*transd[(i-1)*w.ext+1];
        #         else
        #             # Make [[0,1],[-1,0]] in coordinates w.n and w.n+i:
        #             tf:=transd[(i-1)*w.ext+1]^-1*transr[i]*transd[(i-1)*w.ext+1]^-1;
        #         fi;
        #         s := s * tf;
        #         flag := not(flag);
        #     od;

        #     # Finally put together the new 2n-1-cycle and 2n-2-cycle:
        #     s := s^-1;
        #     w.slnstdf[2*w.ext+1] := w.slnstdf[2*w.ext+1] * s;
        #     w.slnstdf[2*w.ext+2] := w.slnstdf[2*w.ext+2] * s;
        #     Unbind(w.transv);
        #     Unbind(w.transh);
        #     w.n := aimdim;
        #     Display("Step 7 done");
        #     return w;
        # fi;

        # Otherwise we do want to go on as the next thing, so we want to
        # keep our transvections. This is easily done if we change the
        # basis one more time. Note that we know that n is odd here!

        # Put together the n-cycle:
        # 2n-1 -> 2n-2 -> ... -> n+1 -> n -> 2n-1
        flag := false;
        s := IdentityMat(d,F);
        #PermMat3 := PermutationMat((4,7,10,6,9,5,8),20,GF(5));
        PermMat3 := RECOG.ComputeCorrectingPermutationMat(d,F,n,aimdim);
        #Display(PermMat3);
        v := Zero(F) * IdentityMat( d, F );
        v[n/2][1] := One(F);
        v{[1..(n/2)-1]}{[2..n/2]} := IdentityMat((n/2)-1,F);
        v[n/2+1][n] := One(F);
        v{[(n/2)+2..n]}{[(n/2)+1..n-1]} := IdentityMat((n/2)-1,F);
        v{[n+1..d]}{[n+1..d]} := IdentityMat(d-n,F);
        #Display(t);
        #Display(t^basechange in G);
        #PermMat3 := PermutationMat((3,5)(6,4),20,GF(5));
        # w.ext = 2?
        #for i in [n-1,n-3..1] do
        #for i in [Size(transr)-1,Size(transr)-3..5] do
        for i in [n-2,n-3..(n/2)] do
            if flag then
                # Make [[0,-1],[1,0]] in coordinates w.n and w.n+i:
                # TODO: Replace 2 by size of extension to get the correct matrices of transd (we want the ones with 1 and -1 at the transvection positions)
                tf := transd[(i-1)*ext+1]*transr[i]^-1*transd[(i-1)*ext+1];
            else
                # Make [[0,1],[-1,0]] in coordinates w.n and w.n+i:
                # TODO: Replace 2 by size of extension to get the correct matrices of transd (we want the ones with 1 and -1 at the transvection positions)
                tf := transd[(i-1)*ext+1]^-1*transr[i]*transd[(i-1)*ext+1]^-1;
            fi;
            #Display(tf);
            #Display((tf^(v^2))^(PermMat3^(-1)));
            #Display(tf);
            s := s * tf;
            flag := not(flag);
        od;

        #Display(((v*s)^(-1))^(PermMat3));
        newbasechange := PermMat3^(-1)*basechange;
        # Now compute v*s
        #Info(InfoRecog,2,"Step 7 done");
        Error("here");

        # # Finally put together the new 2n-1-cycle and 2n-2-cycle:
        # w.slnstdf[2*w.ext+1] := s * w.slnstdf[2*w.ext+1];
        # w.slnstdf[2*w.ext+2] := s * w.slnstdf[2*w.ext+2];

        # list := Concatenation([1..w.n-1],[w.n+1..2*w.n-1],[w.n],[2*w.n..w.d]);
        # perm := PermList(list);
        # mat := PermutationMat(perm^-1,w.d,w.f);
        # ConvertToMatrixRep(mat,w.f);
        # w.bas := w.bas{list};
        # ConvertToMatrixRep(w.bas,w.f);
        # w.basi := w.basi*mat;

        # # Now add the new transvections:
        # for i in [1..w.n-1] do
        #     w.transh[w.ext*(w.n-1)+w.ext*(i-1)+1] := transr[i];
        # od;
        # Append(w.transv,transd);
        # w.n := 2*w.n-1;

        #if( aimdim = 5) then
        #  Error("here");
        #fi;
    fi;

    Info(InfoRecog,2,"Step 7 done");
    # return w;
end;









RECOG.WriteUpperKillerAsWordSU := function(L,n,d,onef,trans1,trans2,diag,v,u,s,q,f,alpha,p,phi)
local tf, value, i, j, omega, basis, coeffs, coeff, trans, shift, one, t, turn, V, q1;

    #one := IdentityMat(n,GF(q));
    shift := v*u;

    omega := PrimitiveElement(GF(q));
    basis := [1..f];
    for i in [0..f-1] do
        basis[i+1] := omega^i;
    od;
    basis := Basis(GF(q),basis);

    for i in [2..(n/2)] do
        value := L[1,i];
        coeffs := Coefficients(basis,value);
        for j in [1..f] do
            coeff := Int(coeffs[j]);
            onef := onef * trans1[(i-2)*f+j]^coeff;
        od;
        #t := IdentityMat(n,GF(q));
        #t[1,i] := value;
        #t[n-i+1,n] := -1*value;
        #one := one*t;
    od;

    for i in [2..(n/2)] do
        value := L[1,(n/2)+i-1];
        coeffs := Coefficients(basis,value);
        for j in [1..f] do
            coeff := Int(coeffs[j]);
            onef := onef * trans2[(i-2)*f+j]^coeff;
        od;
        #t := IdentityMat(n,GF(q));
        #t[1,(n/2)+i-1] := value;
        #t[n-((n/2)+i-1)+1,n] := value;
        #one := one*t;
    od;

    value := L[1,n]-RECOG.ComputeCornerEntrySU2((L{[1]}{[2..n-1]})[1],n-2,GF(q),phi);

    #value := L[1,n]-one[1,n];
    basis := [1..(f/2)-1];
    q1 := Sqrt(q);
    for i in [0..(f/2)-1] do
        basis[i+1] := alpha^(-q1)*(omega^(q1+1))^i;
    od;
    V := VectorSpace(GF(p),basis);
    basis := Basis(V,basis);
    coeffs := Coefficients(basis,value);
    for j in [1..f/2] do
        coeff := Int(coeffs[j]);
        onef := onef * diag[j]^coeff;
    od;

    return onef;

end;


RECOG.WriteUpperKillerAsWordSU2 := function(L,n,d,onef,trans1,trans2,diag,v,u,s,q,f,alpha,p,phi)
local tf, value, i, j, omega, basis, coeffs, coeff, trans, shift, one, t, turn, V, q1;

    #one := IdentityMat(n,GF(q));
    shift := v*u;

    omega := PrimitiveElement(GF(q));
    basis := [1..f];
    for i in [0..f-1] do
        basis[i+1] := omega^i;
    od;
    basis := Basis(GF(q),basis);

    for i in [2..(n/2)] do
        value := L[1,i];
        coeffs := Coefficients(basis,value);
        for j in [1..f] do
            coeff := Int(coeffs[j]);
            onef := onef * trans1[(i-2)*f+j]^coeff;
        od;
        #t := IdentityMat(n,GF(q));
        #t[1,i] := value;
        #t[n-i+1,n] := -1*value;
        #one := one*t;
    od;

    for i in [2..(n/2)] do
        value := L[1,(n/2)+i-1];
        coeffs := Coefficients(basis,value);
        for j in [1..f] do
            coeff := Int(coeffs[j]);
            onef := onef * trans2[(i-2)*f+j]^coeff;
        od;
        #t := IdentityMat(n,GF(q));
        #t[1,(n/2)+i-1] := value;
        #t[n-((n/2)+i-1)+1,n] := value;
        #one := one*t;
    od;

    value := RECOG.ComputeCornerEntrySU((L{[1]}{[2..n-1]})[1],n-2,GF(q),phi);

    return [onef,value];

end;




RECOG.WriteLowerKillerAsWordSU := function(L,n,d,onef,trans1,trans2,diag,v,u,s,q,f,alpha,p,phi)
local tf, value, i, j, omega, basis, coeffs, coeff, trans, shift, one, t, turn, V, q1;

    #one := IdentityMat(n,GF(q));
    shift := v*u;

    omega := PrimitiveElement(GF(q));
    basis := [1..f];
    for i in [0..f-1] do
        basis[i+1] := omega^i;
    od;
    basis := Basis(GF(q),basis);

    for i in [2..(n/2)] do
        value := L[i,1];
        coeffs := Coefficients(basis,value);
        for j in [1..f] do
            coeff := Int(coeffs[j]);
            onef := onef * trans1[(i-2)*f+j]^coeff;
        od;
        #t := IdentityMat(n,GF(q));
        #t[i,1] := value;
        #t[n,n-i+1] := -1*value;
        #one := one*t;
    od;

    for i in [2..(n/2)] do
        value := L[(n/2)+i-1,1];
        coeffs := Coefficients(basis,value);
        for j in [1..f] do
            coeff := Int(coeffs[j]);
            onef := onef * trans2[(i-2)*f+j]^coeff;
        od;
        #t := IdentityMat(n,GF(q));
        #t[(n/2)+i-1,1] := value;
        #t[n,n-((n/2)+i-1)+1] := value;
        #one := one*t;
    od;

    q1 := Sqrt(q);
    value := alpha*alpha^q1*(L[n,1]-(RECOG.ComputeCornerEntrySU((TransposedMat(L){[1]}{[2..n-1]})[1],n-2,GF(q),phi))); 
    #value := -1*(L[n,1]-one[n,1]);
    basis := [1..(f/2)-1];
    for i in [0..(f/2)-1] do
        basis[i+1] := alpha^(-q1)*(omega^(q1+1))^i;
    od;
    V := VectorSpace(GF(p),basis);
    basis := Basis(V,basis);
    coeffs := Coefficients(basis,value);
    turn := diag[1]^0;
    for j in [1..f/2] do
        coeff := Int(coeffs[j]);
        turn := turn * diag[j]^coeff;
    od;
    turn := turn^s;
    onef := onef*turn;

    return onef;

end;


RECOG.WriteLowerKillerAsWordSU2 := function(L,n,d,onef,trans1,trans2,diag,v,u,s,q,f,alpha,p,phi)
local tf, value, i, j, omega, basis, coeffs, coeff, trans, shift, one, t, turn, V;

    #one := IdentityMat(n,GF(q));
    shift := v*u;

    omega := PrimitiveElement(GF(q));
    basis := [1..f];
    for i in [0..f-1] do
        basis[i+1] := omega^i;
    od;
    basis := Basis(GF(q),basis);

    for i in [2..(n/2)] do
        value := L[i,1];
        coeffs := Coefficients(basis,value);
        for j in [1..f] do
            coeff := Int(coeffs[j]);
            onef := onef * trans1[(i-2)*f+j]^coeff;
        od;
        #t := IdentityMat(n,GF(q));
        #t[i,1] := value;
        #t[n,n-i+1] := -1*value;
        #one := one*t;
    od;

    for i in [2..(n/2)] do
        value := L[(n/2)+i-1,1];
        coeffs := Coefficients(basis,value);
        for j in [1..f] do
            coeff := Int(coeffs[j]);
            onef := onef * trans2[(i-2)*f+j]^coeff;
        od;
        #t := IdentityMat(n,GF(q));
        #t[(n/2)+i-1,1] := value;
        #t[n,n-((n/2)+i-1)+1] := value;
        #one := one*t;
    od;

    value := RECOG.ComputeCornerEntrySU((TransposedMat(L){[1]}{[2..n-1]})[1],n-2,GF(q),phi);

    return [onef,value];

end;



RECOG.ComputeCornerEntrySU := function(list, length, F, phi)
local value, i;

    value := Zero(F);
    for i in [1..length/2] do
        value := value + -1*(list[i])^phi * (list[length-i+1]);
    od;

    return value;

end;



RECOG.ComputeCornerEntrySU2 := function(list, length, F, phi)
local value, i;

    value := Zero(F);
    for i in [1..length/2] do
        value := value + (list[i]) * -1*(list[length-i+1])^phi;
    od;

    return value;

end;



RECOG.ComputeCornerEntryProductSU := function(list1, list2, entry, F, k)
local skalar, times;

    if k >= 2 then
        skalar := list1 * list2;
        times := (k-1)*(k)/2;
        return k*entry+skalar*times;
    else
        return entry;
    fi;

end;



# change input into H again
RECOG.SUn_UpStepWithSLP := function(w)
# w has components:
#   d       : size of big SL
#   n       : size of small SL
#   slnstdf : fakegens for SL_n standard generators
#   bas     : current base change, first n vectors are where SL_n acts
#             rest of vecs are invariant under SL_n
#   basi    : current inverse of bas
#   sld     : original group with memory generators, PseudoRandom
#             delivers random elements
#   sldf    : fake generators to keep track of what we are doing
#   f       : field
# The following are filled in automatically if not already there:
#   p       : characteristic
#   ext     : q=p^ext
#   One     : One(slnstdf[1])
#   can     : CanonicalBasis(f)
#   canb    : BasisVectors(can)
#   transh  : fakegens for the "horizontal" transvections n,i for 1<=i<=n-1
#             entries can be unbound in which case they are made from slnstdf
#   transv  : fakegens for the "vertical" transvections i,n for 1<=i<=n-1
#             entries can be unbound in which case they are made from slnstdf
#
# We keep the following invariants (going from n -> n':=2n-1)
#   bas, basi is a base change to the target base
#   slnstdf are SLPs to reach standard generators of SL_n from the
#       generators of sld
local d, id, q, p, F, t, GM, counter, aimdim, newdim, c1, c, ci, sum1, int1, i, v1, v2, v3, L1, L2, newpart, zerovec, MB, newbas, newbasi, int3, pivots, cii, pivots2, 
      newbasechange, trans, tf, lambda, killer, transr, gamma1, gamma2, gamma3, gamma4, gamma0, zeta, k, beta, vectorw, normx, PermMat, PermMat2, HBig, HBigGens, H2n, HSmall, transd,
      WrongForm, ChangeToCorrectForm, ChangeToCorrectFormBig, extract, ChangeToCorrectForm2, ChangeToCorrectFormBig2, FormValue, killervalue, killersupport, vectorlist, VC, VCBasis, 
      LinearCombinationVector, s, flag, v, PermMat3, fixv, factors, ext, vectorlistindex, vectorlist2, vectorlistele, indexlist, VCBuildBasis, CanonicalVC, n, phi, basechange, G, H,
      shift, pos, initele, pos2, tw, alpha, alphad, primitive, basis, shiftele, coeffs, j, coeff, cw, L1w, L2w, cwi, slp, c1w, ciT, HFake, transw, vectorlistscalar, tfw, killerw, storeposition,
      diagonalentrylist, currentvector, tfvalue, difftransv, begintransv, newtransv;

    Info(InfoRecog,3,"Going up: ",w.n," (",w.d,")...");

    # Before we begin, we upgrade the data structure with a few internal
    # things:

    H := GroupByGenerators(w.sunstdf);
    G := w.sld;
    n := w.n;
    phi := w.phi;
    basechange := w.bas;

    d := w.d;
    p := w.p;
    ext := w.ext;
    q := p^ext;
    F := GF(q);

    primitive := PrimitiveElement(GF(q));
    alpha := w.alpha;
    alphad := alpha^(-Sqrt(q));

    basis := [1..ext];
    for i in [0..ext-1] do
        basis[i+1] := primitive^i;
    od;
    basis := Basis(F,basis);

    if not(IsBound(w.can)) then w.can := CanonicalBasis(w.f); fi;
    if not(IsBound(w.canb)) then w.canb := BasisVectors(w.can); fi;
    if not(IsBound(w.One)) then w.One := One(w.sunstdf[1]); fi;
    if not(IsBound(w.transh1)) then w.transh1 := []; fi;
    if not(IsBound(w.transv1)) then w.transv1 := []; fi;
    w.transv2 := [];
    w.transh2 := [];

    for k in [1..w.ext] do
        pos := k;
        if not(IsBound(w.transh1[pos])) then
            w.transh1[pos] := w.sunstdf[k];
        fi;
        if not(IsBound(w.transv1[pos])) then
            w.transv1[pos] := w.sunstdf[w.ext + k];
        fi;
    od;

    shift := w.sunstdf[2*w.ext + (w.ext/2) + 1] * w.sunstdf[2*w.ext + (w.ext/2) + 2];
    for i in [3..(w.n)/2] do
        for k in [1..w.ext] do
            pos := (i-2)*w.ext + k;
            if not(IsBound(w.transh1[pos])) then
                # TODO: Remove initele
                initele := One(w.sunstdf[1]);
                initele := (initele * w.transh1[pos-w.ext])^shift;
                w.transh1[pos] := initele;
            fi;
            if not(IsBound(w.transv1[pos])) then
                # TODO: Remove initele
                initele := One(w.sunstdf[1]);
                initele := (initele * w.transv1[pos-w.ext])^shift;
                w.transv1[pos] := initele;
            fi;
        od;
    od;

    for k in [1..w.ext] do
        pos := k;
        if not(IsBound(w.transv2[pos])) then
            initele := One(w.sunstdf[1]);
            beta := -1*(primitive^(k-1))^phi*alpha;
            shiftele := One(w.sunstdf[1]);
            coeffs := Coefficients(basis,beta);
            for j in [1..ext] do
                coeff := Int(coeffs[j]);
                shiftele := shiftele * w.transh1[((w.n)/2-2)*w.ext+j]^coeff;
            od;
            initele := (initele * shiftele)^w.sunstdf[2*w.ext + (w.ext/2) + 3];
            w.transv2[pos] := initele;
        fi;
        if not(IsBound(w.transh2[pos])) then
            initele := One(w.sunstdf[1]);
            beta := -1*(primitive^(k-1))^phi*alpha^(-1);
            shiftele := One(w.sunstdf[1]);
            coeffs := Coefficients(basis,beta);
            for j in [1..ext] do
                coeff := Int(coeffs[j]);
                shiftele := shiftele * w.transv1[((w.n)/2-2)*w.ext+j]^coeff;
            od;
            initele := (initele * shiftele)^w.sunstdf[2*w.ext + (w.ext/2) + 3];
            w.transh2[pos] := initele;
        fi;
    od;

    shift := shift^(-1);
    for i in [3..(w.n)/2] do
        for k in [1..w.ext] do
            pos := (i-2)*w.ext + k;
            if not(IsBound(w.transh2[pos])) then
                initele := One(w.sunstdf[1]);
                initele := (initele * w.transh2[pos-w.ext])^shift;
                w.transh2[pos] := initele;
            fi;
            if not(IsBound(w.transv2[pos])) then
                initele := One(w.sunstdf[1]);
                initele := (initele * w.transv2[pos-w.ext])^shift;
                w.transv2[pos] := initele;
            fi;
        od;
    od;

    # Here everything starts, some more preparations:

    # We compute exclusively in our basis, so we occasionally need an
    # identity matrix:
    id := IdentityMat(d,F);

    Info(InfoRecog,2,"Current dimension: " );
    Info(InfoRecog,2,n);
    Info(InfoRecog,2,"\n");
    Info(InfoRecog,2,"New dimension: ");
    Info(InfoRecog,2,Minimum(2*n-2,d));
    Info(InfoRecog,2,"\n");

    Info(InfoRecog,2,"Preparation done.");

    # Next step also correct for characteristic 2?
    if p = 2 then
        Error("todo");
    else
        t := PermutationMat(CycleFromList([1..n/2])*CycleFromList(Reversed([(n/2)+1..n])),d,F);
        tw := w.sunstdf[2*w.ext + (w.ext/2)+1];
    fi;

    Info(InfoRecog,2,"Step 1 done.");

    # Find a good random element:
    w.count := 0;
    aimdim := Minimum(2*n-2,d);
    newdim := aimdim - n;
    counter := 0;

    Info(InfoRecog,2,"Step 1 done.");

    # Find a good random element:
    while true do   # will be left by break
        while true do    # will be left by break
            counter := counter + 1;
            if InfoLevel(InfoRecog) >= 3 then Print(".\c"); fi;
            c1 := PseudoRandom(G);
            
            # Do the base change into our basis:
            c := t^(w.bas * c1 * w.basi);
            
            # Now check that Vn + Vn*s^c1 has dimension 2n-1:
            sum1 := SumIntersectionMat(c{[1..n]},id{[1..n]});
   
            if Size(sum1[1]) = aimdim then

                int1 := SumIntersectionMat(RECOG.FixspaceMat(c),id{[1..n]})[2];

                for i in [1..Size(int1)] do
                    v1 := int1[i];
                    if not(IsZero(v1[1])) then break; fi;
                od;
                for i in [1..Size(int1)] do
                    v2 := int1[i];
                    if (v1 <> v2) and not(IsZero(v2[n])) then break; fi;
                od;
                if (v1 = v2) or IsZero(v1[1]) or IsZero(v2[n]) then
                    Info(InfoRecog,2,"Ooops: Component n was zero!");
                    continue;
                fi;

                v1 := v1 / v1[1];   # normalize to 1 in position 1
                Assert(1,v1*c=v1);

                v2 := v2 / v2[n];   # normalize to 1 in position n
                Assert(1,v2*c=v2);

                v1 := v1 + (-1) * v1[n] * v2;
                v2 := v2 + (-1) * v2[1] * v1;

                # Actually we don't need gamma3 here
                gamma1 := Zero(F);
                gamma2 := One(F);
                gamma3 := One(F);
                gamma4 := Zero(F);
                for k in [2..n-1] do
                    gamma1 := gamma1 + v2[k]*(v2[n-k+1])^phi;
                od;

                if gamma1 = Zero(F) then
                    Info(InfoRecog,2,"Ooops: gamma1 was zero!");
                    continue;
                fi;

                for k in [2..n-1] do
                    gamma4 := gamma4 + v1[k]*(v1[n-k+1])^phi;
                od;
                for k in [2..n-1] do
                    gamma2 := gamma2 + v2[k]*(v1[n-k+1])^phi;
                od;
                for k in [2..n-1] do
                    gamma3 := gamma3 + v1[k]*(v2[n-k+1])^phi;
                od;

                gamma0 := RECOG.SolveNormEquationSilly(F,phi,gamma1);
                zeta := gamma2*gamma0^(-1);
                normx := RECOG.SolveNormEquationSilly(F,phi,zeta*zeta^phi-gamma4);

                if zeta*zeta^phi-gamma4 = Zero(F) then
                    Info(InfoRecog,2,"Ooops: zeta*zeta^phi-gamma4 was zero!");
                    continue;
                fi;

                beta := (normx-zeta^phi)*gamma0^(-1);

                vectorw := v1 + beta * v2;

                L1 := IdentityMat(d,F);
                for i in [2..n-1] do
                    L1[1,i] := vectorw[i];
                    L1[n-i+1,n] := -1*vectorw[i]^phi;
                od;
                L1[1,n] := beta;

                if not(L1^basechange in SU(d,Sqrt(q))) then
                    Info(InfoRecog,2,"Ooops: Component not useable!");
                    Print("foul play");
                    Error("here");
                    continue;
                fi;

                c := L1*c*L1^(-1);
                int1 := SumIntersectionMat(RECOG.FixspaceMat(c),id{[1..n]})[2];
                for i in [1..Size(int1)] do
                    v2 := int1[i];
                    if not(IsZero(v2[n])) then break; fi;
                od;

                if IsZero(v2[n]) then
                    Info(InfoRecog,2,"Ooops: Component n was zero!");
                    continue;
                fi;

                v1 := id[1];
                v2 := v2 / v2[n];   # normalize to 1 in position n
                Assert(1,v2*c=v2);

                v2 := v2 + (-1) * v2[1] * v1;

                gamma1 := Zero(F);
                for k in [2..n-1] do
                    gamma1 := gamma1 + v2[k]*(v2[n-k+1])^phi;
                od;
                normx := RECOG.SolveNormEquationSilly(F,phi,gamma1);
                beta := RECOG.SolveMyBachelorEquationSilly(F,phi,normx);

                vectorw := v2 + beta * v1;

                L2 := IdentityMat(d,F);
                for i in [2..n-1] do
                    L2[n,i] := vectorw[i];
                    L2[n-i+1,1] := -1*vectorw[i]^phi;
                od;
                L2[n,1] := beta;

                if not(L2^basechange in SU(d,Sqrt(q))) then
                    Info(InfoRecog,2,"Ooops: Component not useable!");
                    Print("foul play");
                    Error("here");
                    continue;
                fi;

                c := L2*c*L2^(-1);
                ci := c^-1;
                break;
            fi;
            # Display(counter);
        od;

        # We have to write L1 and L2 as words in spnstdf
        L1w := RECOG.WriteUpperKillerAsWordSU(L1,n,d,w.One,w.transh1,w.transh2,w.sunstdf{[2*ext+1..(2*ext+ext/2)]},w.sunstdf[2*w.ext + (w.ext/2)+1],w.sunstdf[2*w.ext + (w.ext/2)+2],w.sunstdf[2*w.ext + (w.ext/2)+3],q,ext,alpha,p,phi);
        L2w := RECOG.WriteLowerKillerAsWordSU(L2,n,d,w.One,w.transv1,w.transv2,w.sunstdf{[2*ext+1..(2*ext+ext/2)]},w.sunstdf[2*w.ext + (w.ext/2)+1],w.sunstdf[2*w.ext + (w.ext/2)+2],w.sunstdf[2*w.ext + (w.ext/2)+3],q,ext,alpha,p,phi);

        # Save the SLP for c
        slp := SLPOfElm(c1);
        c1w := ResultOfStraightLineProgram(slp,w.sldf);
        cw := tw^c1w;
        cw := L1w*cw*L1w^(-1);
        cw := L2w*cw*L2w^(-1);
        cwi := cw^-1;
        
        Info(InfoRecog,2,"Step 2 done.");

        # Now we found our aimdim-dimensional space W. Since SL_n
        # has a d-n-dimensional fixed space W_{d-n} and W contains a complement
        # of that fixed space, the intersection of W and W_{d-n} has dimension
        # newdim.

        # Change basis:
        newpart := ExtractSubMatrix(c,[2..(n-1)],[1..(d)]);
        # Clean out the first n entries to go to the fixed space of SL_n:
        zerovec := Zero(newpart[1]);
        for i in [1..(n-2)] do
            CopySubVector(zerovec,newpart[i],[1..n],[1..n]);
        od;
        MB := MutableBasis(F,[],zerovec);
        i := 1;
        pivots := EmptyPlist(newdim);
        while i <= Length(newpart) and NrBasisVectors(MB) < newdim do
            if not(IsContainedInSpan(MB,newpart[i])) then
                Add(pivots,i);
                CloseMutableBasis(MB,newpart[i]);
            fi;
            i := i + 1;
        od;

        newpart := newpart{pivots};
        newbas := Concatenation(id{[1..n]},newpart);
        if 2*n-2 < d then

            int3 := SumIntersectionMat(RECOG.FixspaceMat(c),id{[n+1..d]})[2];
            
            if Size(int3) <> d - aimdim then
                Info(InfoRecog,2,"Ooops, FixSLn \cap Fixc wrong dimension");
                #Error("neues beispiel");
                continue;
            fi;
            Append(newbas,int3);

        fi;
        ConvertToMatrixRep(newbas,Size(F));
        newbasi := newbas^-1;
        if newbasi = fail then
            Info(InfoRecog,2,"Ooops, Fixc intersected too much, we try again");
            continue;
        fi;
        
        ci := newbas * ci * newbasi;

        cii := ExtractSubMatrix(ci,[n+1..aimdim],[2..n-1]);
        ConvertToMatrixRep(cii,Size(F));
        cii := TransposedMat(cii);
        # The rows of cii are now what used to be the columns,
        # their length is newdim, we need to span the full newdim-dimensional
        # row space and need to remember how:
        zerovec := Zero(cii[1]);
        MB := MutableBasis(F,[],zerovec);
        i := 1;
        pivots2 := EmptyPlist(newdim);
        while i <= Length(cii) and NrBasisVectors(MB) < newdim do
            if not(IsContainedInSpan(MB,cii[i])) then
                Add(pivots2,i);
                CloseMutableBasis(MB,cii[i]);
            fi;
            i := i + 1;
        od;
        if Length(pivots2) = newdim then
            cii := cii{pivots2}^-1;
            ConvertToMatrixRep(cii,F);

            c := newbas * c * newbasi;
            newbasechange := newbas*basechange;
            w.bas := newbas * w.bas;
            w.basi := w.basi * newbasi;
            break;
        fi;
        Info(InfoRecog,2,"Ooops, no nice bottom...");
        # Otherwise simply try again
    od;

    Info(InfoRecog,2,"Begin with form change");

    HFake := RECOG.LiftGroup(GeneratorsOfGroup(SU(n,Sqrt(q))),n,q,d)[1];
    HBigGens := List(GeneratorsOfGroup(HFake),MutableCopyMat);
    Append(HBigGens,GeneratorsOfGroup(HFake^c));
    HBig := GroupByGenerators(HBigGens);
    basechange := newbasechange;
    #Display(RecogniseClassical(RECOG.LinearActionRepresentation(HBig)));
    HSmall := GroupByGenerators(List(GeneratorsOfGroup(HBig),x->x{[1..aimdim]}{[1..aimdim]}));
    WrongForm := PreservedSesquilinearForms(HSmall)[1];
    extract := HermitianFormByMatrix((WrongForm!.matrix){[n+1..aimdim]}{[n+1..aimdim]}, F );
    FormValue := (WrongForm!.matrix)[1,n];
    ChangeToCorrectForm := BaseChangeToCanonical(extract);
    ChangeToCorrectFormBig := IdentityMat(aimdim,F);
    ChangeToCorrectFormBig{[n+1..aimdim]}{[n+1..aimdim]} := ChangeToCorrectForm;

    PermMat := One(SymmetricGroup(aimdim));
    if IsEvenInt(aimdim) then
        for i in [1..(n/2)] do
            PermMat := PermMat*(i,n-i+1);
        od;
        for i in [n+1..(n+aimdim)/2] do
            PermMat := PermMat*(i,aimdim-i+n+1);
        od;
        PermMat := PermutationMat(PermMat,d,F);
        PermMat2 := One(SymmetricGroup(aimdim));
        for i in [1..aimdim/2] do
            PermMat2 := PermMat2*(i,aimdim-i+1);
        od;
        PermMat2 := PermutationMat(PermMat2,d,F);
    else
        for i in [1..(n/2)] do
            PermMat := PermMat*(i,n-i+1);
        od;
        for i in [n+1..(n-1+aimdim)/2] do
            PermMat := PermMat*(i,aimdim-i+n+1);
        od;
        PermMat := PermutationMat(PermMat,d,F);
        PermMat2 := One(SymmetricGroup(aimdim));
        for i in [1..(aimdim-1)/2] do
            PermMat2 := PermMat2*(i,aimdim-i+1);
        od;
        PermMat2 := PermutationMat(PermMat2,d,F);
    fi;

    WrongForm := IdentityMat(aimdim,F);
    WrongForm{[n+1..aimdim]}{[n+1..aimdim]} := FormValue*PermMat{[n+1..aimdim]}{[n+1..aimdim]};
    ChangeToCorrectForm2 := BaseChangeToCanonical(HermitianFormByMatrix(WrongForm, F ));
    ChangeToCorrectFormBig2 := IdentityMat(d,F);
    ChangeToCorrectFormBig2{[1..aimdim]}{[1..aimdim]} := ChangeToCorrectFormBig^(-1)*ChangeToCorrectForm2;
    HBig := HBig^ChangeToCorrectFormBig2;
    c := ChangeToCorrectFormBig2^(-1) * c * ChangeToCorrectFormBig2;
    basechange := ChangeToCorrectFormBig2^(-1)*basechange;
    w.bas := ChangeToCorrectFormBig2^(-1) * w.bas;
    w.basi := w.basi * ChangeToCorrectFormBig2;

    ci := c^-1;
    ciT := TransposedMat(ci);

    Info(InfoRecog,2,"End of form change");

    # Now consider the transvections t_i:
    # t_i : w.bas[j] -> w.bas[j]        for j <> i and
    # t_i : w.bas[i] -> w.bas[i] + ww
    # We want to modify (t_i)^c such that it fixes w.bas{[1..w.n]}:

    trans := [];
    transw := [];
    vectorlist := [];
    vectorlistscalar := [];

    # If we are finishing up, we have to make sure, that the pivot elements are really pivot elements for the horizontal transvections. 
    # Otherwise we have to choose different pivots
    if aimdim = w.GoalDim then
        cii := ExtractSubMatrix(ci,[n+1..aimdim],[2..n-1]);
        ConvertToMatrixRep(cii,Size(F));
        cii := TransposedMat(cii);
        zerovec := Zero(cii[1]);
        MB := MutableBasis(F,[],zerovec);
        i := 1;
        pivots2 := EmptyPlist(newdim);
        while i <= Length(cii) and NrBasisVectors(MB) < newdim do
            if not(IsContainedInSpan(MB,cii[i])) then
                Add(pivots2,i);
                CloseMutableBasis(MB,cii[i]);
            fi;
            i := i + 1;
        od;
        if NrBasisVectors(MB) < newdim then
            Error("this should not happen");
        fi;
    fi;

    if not(IsEvenInt(aimdim)) then
        trans := [];
        vectorlist := [];
        diagonalentrylist := [];
        for i in pivots2 do
            # This does t_i
            for lambda in w.canb do
                # This does t_i : v_j -> v_j + lambda * v_n
                tf := IdentityMat(d,F);
                tf{[2..n-1]}{[n]} := (lambda)^phi * ci{[2..n-1]}{[i+1]};
                tf{[1]}{[2..n-1]} := [Reversed(TransposedMat(-1*tf{[2..n-1]}{[n]}^phi)[1])];
                Add(vectorlistscalar,-1*lambda * c[n-i]{[n+1..aimdim]});
                if i+1 <= n/2 then
                    tfw := w.One*w.transh2[Size(w.transh2)-(i*w.ext)+Position(w.canb,lambda)]^(-1);
                else
                    tfw := (w.One*w.transh1[Size(w.transh1)-((i-n/2+1)*w.ext)+Position(w.canb,lambda)])^(-1);
                fi;

                # Now conjugate with c:
                tfw := cwi*tfw*cw;

                # Now cleanup in column n above row n, the entries there
                # are lambda times the stuff in column i of ci:
                #for j in [1..w.n-1] do
                #    tf := DoRowOp_n(tf,j,w.n,-ci[j,i]*lambda,w);
                #od;
                # Now cleanup in column n above row n, the entries there
                killerw := RECOG.WriteUpperKillerAsWordSU2(tf{[1..n]}{[1..n]}^(-1),n,d,w.One,w.transh1,w.transh2,w.sunstdf{[2*ext+1..(2*ext+ext/2)]},w.sunstdf[2*w.ext + (w.ext/2)+1],w.sunstdf[2*w.ext + (w.ext/2)+2],w.sunstdf[2*w.ext + (w.ext/2)+3],q,ext,alpha,p,phi);
                Add(diagonalentrylist,-1*killerw[2]);
                killerw := killerw[1];
                tfw := killerw*tfw;
                Add(vectorlist, lambda^phi * ciT[i+1]{[n+1..aimdim]});
                Add(trans,tf);
                Add(transw,tfw);
            od;
        od;

        # For now vector space variant. but change that!
        VC := VectorSpace(GF(p),vectorlist);
        VCBasis := Basis(VC,vectorlist);
        ConvertToMatrixRep(vectorlist,F);
        ConvertToMatrixRep(vectorlistscalar,F);

        # Now put together the clean ones by our knowledge of c^-1:
        transd := [];
        CanonicalVC := BasisVectors(CanonicalBasis(VC));
        for i in CanonicalVC do
            LinearCombinationVector := Coefficients(VCBasis,i);
            tf := IdentityMat(d,F);
            tfw := w.One;
            tfvalue := Zero(F);
            currentvector := Zero(VC);
            for lambda in [1..Size(LinearCombinationVector)] do
                if LinearCombinationVector[lambda] <> Zero(F) then
                    #Display(tfvalue);
                    #Display(diagonalentrylist[lambda]);
                    #Display(RECOG.ComputeCornerEntryProductSU(vectorlist[lambda], vectorlistscalar[lambda], diagonalentrylist[lambda], F,  Int(LinearCombinationVector[lambda])));
                    #Display(LinearCombinationVector[lambda]*(currentvector*vectorlist[lambda]));
                    #Display(currentvector);
                    tfvalue := tfvalue + LinearCombinationVector[lambda]*(currentvector*vectorlist[lambda]) + RECOG.ComputeCornerEntryProductSU(vectorlist[lambda], vectorlistscalar[lambda], diagonalentrylist[lambda], F,  Int(LinearCombinationVector[lambda]));
                    currentvector := currentvector + LinearCombinationVector[lambda]*vectorlistscalar[lambda];
                    #Display(currentvector);
                    tfw := tfw*transw[lambda]^Int(LinearCombinationVector[lambda]);
                fi;
            od;

            if Position(CanonicalVC, i) = Size(CanonicalVC)/2 then
                storeposition := Position(CanonicalVC, i);
            fi;
            
            if not(Position(CanonicalVC, i) in [Size(CanonicalVC)/2..Size(CanonicalVC)/2 + w.ext - 1]) then
                tf[1,n] := -1*tfvalue;
                #Display(ResultOfStraightLineProgram(SLPOfElm(tfw),GeneratorsOfGroup(SU(20,7)))^(newbasechange^(-1)));
                #Display(tf);

                #Error("more to do to compute diagonalentry");
                #Error("We find the new transvection matrices also where we cannot clear the top right entry");
                killerw := RECOG.WriteUpperKillerAsWordSU(tf{[1..n]}{[1..n]},n,d,w.One,w.transh1,w.transh2,w.sunstdf{[2*ext+1..(2*ext+ext/2)]},w.sunstdf[2*w.ext + (w.ext/2)+1],w.sunstdf[2*w.ext + (w.ext/2)+2],w.sunstdf[2*w.ext + (w.ext/2)+3],q,ext,alpha,p,phi);
                tfw := killerw*tfw;
            fi;

            Add(transd,tfw);
        od;
        Unbind(trans);
        Unbind(transw);

        Info(InfoRecog,2,"Step 5 done");

        # Now to the "horizontal" transvections, first create them as SLPs:
        trans := [];
        transw := [];
        vectorlist := [];
        vectorlistscalar := [];
        diagonalentrylist := [];
        
        # If we are finishing up, we have to make sure, that the pivot elements are really pivot elements for the horizontal transvections. 
        # Otherwise we have to choose different pivots
        if aimdim = w.GoalDim then
            newpart := ExtractSubMatrix(c,[2..n-1],[n+1..aimdim]);
            zerovec := Zero(newpart[1]);
            MB := MutableBasis(F,[],zerovec);
            i := 1;
            pivots := EmptyPlist(newdim);
            while i <= Length(newpart) and NrBasisVectors(MB) < newdim do
                if not(IsContainedInSpan(MB,newpart[i])) then
                    Add(pivots,i);
                    CloseMutableBasis(MB,newpart[i]);
                fi;
                i := i + 1;
            od;
        fi;

        for i in pivots do
            for lambda in w.canb do
                # This does t_i : v_j -> v_j + lambda * v_n
                tf := IdentityMat(d,F);
                tf{[n]}{[2..n-1]} := lambda^phi * c{[i+1]}{[2..n-1]};
                tf{[2..n-1]}{[1]} := TransposedMat([Reversed((-1*tf{[n]}{[2..n-1]}^phi)[1])]);
                Add(vectorlistscalar,-1*lambda * ciT[n-i]{[n+1..aimdim]});
                if i+1 <= n/2 then
                    tfw := w.One*w.transv2[Size(w.transv2)-(i*w.ext)+Position(w.canb,lambda)]^(-1);
                else
                    tfw := (w.One*w.transv1[Size(w.transv1)-((i-n/2+1)*w.ext)+Position(w.canb,lambda)])^(-1);
                fi;

                # Now conjugate with c:
                tfw := cwi*tfw*cw;

                # Now cleanup in column n above row n, the entries there
                # are lambda times the stuff in column i of ci:
                #for j in [1..w.n-1] do
                #    tf := DoRowOp_n(tf,j,w.n,-ci[j,i]*lambda,w);
                #od;
                # Now cleanup in column n above row n, the entries there
                killerw := RECOG.WriteLowerKillerAsWordSU2(tf{[1..n]}{[1..n]}^(-1),n,d,w.One,w.transv1,w.transv2,w.sunstdf{[2*ext+1..(2*ext+ext/2)]},w.sunstdf[2*w.ext + (w.ext/2)+1],w.sunstdf[2*w.ext + (w.ext/2)+2],w.sunstdf[2*w.ext + (w.ext/2)+3],q,ext,alpha,p,phi);
                Add(diagonalentrylist,killerw[2]+(-1*lambda * ciT[n-i]{[n+1..aimdim]})*(lambda^phi * c[i+1]{[n+1..aimdim]}));
                killerw := killerw[1];
                tfw := killerw*tfw;
                Add(vectorlist, lambda^phi * c[i+1]{[n+1..aimdim]});
                Add(trans,tf);
                Add(transw,tfw);
            od;
        od;

        # For now vector space variant. but change that!
        VC := VectorSpace(GF(p),vectorlist);
        VCBasis := Basis(VC,vectorlist);
        ConvertToMatrixRep(vectorlist,F);
        ConvertToMatrixRep(vectorlistscalar,F);

        # Now put together the clean ones by our knowledge of c^-1:
        transr := [];
        CanonicalVC := BasisVectors(CanonicalBasis(VectorSpace(F,IdentityMat(aimdim-n,F))));
        for i in CanonicalVC do
            LinearCombinationVector := Coefficients(VCBasis,i);
            tf := IdentityMat(d,F);
            tfw := w.One;
            tfvalue := Zero(F);
            currentvector := Zero(VC);
            for lambda in [1..Size(LinearCombinationVector)] do
                if LinearCombinationVector[lambda] <> Zero(F) then
                    tfvalue := tfvalue + LinearCombinationVector[lambda]*(currentvector*vectorlistscalar[lambda]) + RECOG.ComputeCornerEntryProductSU(vectorlist[lambda], vectorlistscalar[lambda], diagonalentrylist[lambda], F,  Int(LinearCombinationVector[lambda]));
                    currentvector := currentvector + LinearCombinationVector[lambda]*vectorlist[lambda];
                    tfw := tfw*transw[lambda]^Int(LinearCombinationVector[lambda]);
                fi;
            od;

            if Position(CanonicalVC, i) <> (Size(CanonicalVC)+1)/2 then
                tf[n,1] := -1*tfvalue;
                killerw := RECOG.WriteLowerKillerAsWordSU(tf{[1..n]}{[1..n]},n,d,w.One,w.transv1,w.transv2,w.sunstdf{[2*ext+1..(2*ext+ext/2)]},w.sunstdf[2*w.ext + (w.ext/2)+1],w.sunstdf[2*w.ext + (w.ext/2)+2],w.sunstdf[2*w.ext + (w.ext/2)+3],q,ext,alpha,p,phi);
                tfw := killerw*tfw;
            fi;

            Add(transr,tfw);
        od;
        Unbind(trans);
        Unbind(transw);

        Info(InfoRecog,2,"Step 6 done");

        # Put together the n-cycle:
        # 2n-1 -> 2n-2 -> ... -> n+1 -> n -> 2n-1

        flag := false;
        s := w.One;
        PermMat3 := RECOG.ComputeCorrectingPermutationMatOdd(d,F,n,aimdim);
        v := w.sunstdf[2*w.ext+(w.ext/2)+1];
        
        for i in [aimdim-n,aimdim-n-1..(aimdim-n+1)/2+1] do
            if flag then
                # Make [[0,-1],[1,0]] in coordinates w.n and w.n+i:
                # TODO: Replace 2 by size of extension to get the correct matrices of transd (we want the ones with 1 and -1 at the transvection positions)
                tf := transd[(i-1)*ext+1]*transr[i]^-1*transd[(i-1)*ext+1];
            else
                # Make [[0,1],[-1,0]] in coordinates w.n and w.n+i:
                # TODO: Replace 2 by size of extension to get the correct matrices of transd (we want the ones with 1 and -1 at the transvection positions)
                tf := transd[(i-1)*ext+1]^-1*transr[i]*transd[(i-1)*ext+1]^-1;
            fi;
            #Display(tf);
            #Display((tf^(v^2))^(PermMat3^(-1)));
            #Display(tf);
            s := s * tf;
            flag := not(flag);
        od;

        if flag then
            v := ((w.sunstdf[2*w.ext+(w.ext/2)+4]^((Sqrt(q)-1)/2))^((v*s*w.sunstdf[2*w.ext+(w.ext/2)+3])^(-1)))*(v*s);
        else
            v := (v*s);
        fi;
        w.sunstdf[2*w.ext+(w.ext/2)+1] := v;
        w.myx := transd[storeposition];
        newbasechange := PermMat3^(-1)*basechange;
        w.bas := PermMat3^(-1) * w.bas;
        w.basi := w.basi * PermMat3;
        Unbind(w.transv);
        Unbind(w.transh);
        w.n := aimdim;
        Info(InfoRecog,2,"Step 7 done");
        return w;
    else
        trans := [];
        vectorlist := [];
        diagonalentrylist := [];
        for i in pivots2 do
            # This does t_i
            for lambda in w.canb do
                # This does t_i : v_j -> v_j + lambda * v_n
                tf := IdentityMat(d,F);
                tf{[2..n-1]}{[n]} := (lambda)^phi * ci{[2..n-1]}{[i+1]};
                tf{[1]}{[2..n-1]} := [Reversed(TransposedMat(-1*tf{[2..n-1]}{[n]}^phi)[1])];
                Add(vectorlistscalar,-1*lambda * c[n-i]{[n+1..aimdim]});
                if i+1 <= n/2 then
                    tfw := w.One*w.transh2[Size(w.transh2)-(i*w.ext)+Position(w.canb,lambda)]^(-1);
                else
                    tfw := (w.One*w.transh1[Size(w.transh1)-((i-n/2+1)*w.ext)+Position(w.canb,lambda)])^(-1);
                fi;

                # Now conjugate with c:
                tfw := cwi*tfw*cw;

                # Now cleanup in column n above row n, the entries there
                # are lambda times the stuff in column i of ci:
                #for j in [1..w.n-1] do
                #    tf := DoRowOp_n(tf,j,w.n,-ci[j,i]*lambda,w);
                #od;
                # Now cleanup in column n above row n, the entries there
                killerw := RECOG.WriteUpperKillerAsWordSU2(tf{[1..n]}{[1..n]}^(-1),n,d,w.One,w.transh1,w.transh2,w.sunstdf{[2*ext+1..(2*ext+ext/2)]},w.sunstdf[2*w.ext + (w.ext/2)+1],w.sunstdf[2*w.ext + (w.ext/2)+2],w.sunstdf[2*w.ext + (w.ext/2)+3],q,ext,alpha,p,phi);
                Add(diagonalentrylist,-1*killerw[2]);
                killerw := killerw[1];
                tfw := killerw*tfw;
                Add(vectorlist, lambda^phi * ciT[i+1]{[n+1..aimdim]});
                Add(trans,tf);
                Add(transw,tfw);
            od;
        od;

        # For now vector space variant. but change that!
        VC := VectorSpace(GF(p),vectorlist);
        VCBasis := Basis(VC,vectorlist);
        ConvertToMatrixRep(vectorlist,F);
        ConvertToMatrixRep(vectorlistscalar,F);

        # Now put together the clean ones by our knowledge of c^-1:
        transd := [];
        CanonicalVC := BasisVectors(CanonicalBasis(VC));
        for i in CanonicalVC do
            LinearCombinationVector := Coefficients(VCBasis,i);
            tf := IdentityMat(d,F);
            tfw := w.One;
            tfvalue := Zero(F);
            currentvector := Zero(VC);
            for lambda in [1..Size(LinearCombinationVector)] do
                if LinearCombinationVector[lambda] <> Zero(F) then
                    #Display(tfvalue);
                    #Display(diagonalentrylist[lambda]);
                    #Display(RECOG.ComputeCornerEntryProductSU(vectorlist[lambda], vectorlistscalar[lambda], diagonalentrylist[lambda], F,  Int(LinearCombinationVector[lambda])));
                    #Display(LinearCombinationVector[lambda]*(currentvector*vectorlist[lambda]));
                    #Display(currentvector);
                    tfvalue := tfvalue + LinearCombinationVector[lambda]*(currentvector*vectorlist[lambda]) + RECOG.ComputeCornerEntryProductSU(vectorlist[lambda], vectorlistscalar[lambda], diagonalentrylist[lambda], F,  Int(LinearCombinationVector[lambda]));
                    currentvector := currentvector + LinearCombinationVector[lambda]*vectorlistscalar[lambda];
                    #Display(currentvector);
                    tfw := tfw*transw[lambda]^Int(LinearCombinationVector[lambda]);
                fi;
            od;
            tf[1,n] := -1*tfvalue;
            #Display(ResultOfStraightLineProgram(SLPOfElm(tfw),GeneratorsOfGroup(SU(20,7)))^(newbasechange^(-1)));
            #Display(tf);
            killerw := RECOG.WriteUpperKillerAsWordSU(tf{[1..n]}{[1..n]},n,d,w.One,w.transh1,w.transh2,w.sunstdf{[2*ext+1..(2*ext+ext/2)]},w.sunstdf[2*w.ext + (w.ext/2)+1],w.sunstdf[2*w.ext + (w.ext/2)+2],w.sunstdf[2*w.ext + (w.ext/2)+3],q,ext,alpha,p,phi);
            tfw := killerw*tfw;
            Add(transd,tfw);
        od;
        Unbind(trans);
        Unbind(transw);

        Info(InfoRecog,2,"Step 5 done");

        # Now to the "horizontal" transvections, first create them as SLPs:
        trans := [];
        transw := [];
        vectorlist := [];
        vectorlistscalar := [];
        diagonalentrylist := [];
        
        # If we are finishing up, we have to make sure, that the pivot elements are really pivot elements for the horizontal transvections. 
        # Otherwise we have to choose different pivots
        if aimdim = w.GoalDim then
            newpart := ExtractSubMatrix(c,[2..n-1],[n+1..aimdim]);
            zerovec := Zero(newpart[1]);
            MB := MutableBasis(F,[],zerovec);
            i := 1;
            pivots := EmptyPlist(newdim);
            while i <= Length(newpart) and NrBasisVectors(MB) < newdim do
                if not(IsContainedInSpan(MB,newpart[i])) then
                    Add(pivots,i);
                    CloseMutableBasis(MB,newpart[i]);
                fi;
                i := i + 1;
            od;
        fi;

        for i in pivots do
            for lambda in w.canb do
                # This does t_i : v_j -> v_j + lambda * v_n
                tf := IdentityMat(d,F);
                tf{[n]}{[2..n-1]} := lambda^phi * c{[i+1]}{[2..n-1]};
                tf{[2..n-1]}{[1]} := TransposedMat([Reversed((-1*tf{[n]}{[2..n-1]}^phi)[1])]);
                Add(vectorlistscalar,-1*lambda * ciT[n-i]{[n+1..aimdim]});
                if i+1 <= n/2 then
                    tfw := w.One*w.transv2[Size(w.transv2)-(i*w.ext)+Position(w.canb,lambda)]^(-1);
                else
                    tfw := (w.One*w.transv1[Size(w.transv1)-((i-n/2+1)*w.ext)+Position(w.canb,lambda)])^(-1);
                fi;

                # Now conjugate with c:
                tfw := cwi*tfw*cw;

                # Now cleanup in column n above row n, the entries there
                # are lambda times the stuff in column i of ci:
                #for j in [1..w.n-1] do
                #    tf := DoRowOp_n(tf,j,w.n,-ci[j,i]*lambda,w);
                #od;
                # Now cleanup in column n above row n, the entries there
                killerw := RECOG.WriteLowerKillerAsWordSU2(tf{[1..n]}{[1..n]}^(-1),n,d,w.One,w.transv1,w.transv2,w.sunstdf{[2*ext+1..(2*ext+ext/2)]},w.sunstdf[2*w.ext + (w.ext/2)+1],w.sunstdf[2*w.ext + (w.ext/2)+2],w.sunstdf[2*w.ext + (w.ext/2)+3],q,ext,alpha,p,phi);
                Add(diagonalentrylist,killerw[2]+(-1*lambda * ciT[n-i]{[n+1..aimdim]})*(lambda^phi * c[i+1]{[n+1..aimdim]}));
                killerw := killerw[1];
                tfw := killerw*tfw;
                Add(vectorlist, lambda^phi * c[i+1]{[n+1..aimdim]});
                Add(trans,tf);
                Add(transw,tfw);
            od;
        od;

        # For now vector space variant. but change that!
        VC := VectorSpace(GF(p),vectorlist);
        VCBasis := Basis(VC,vectorlist);
        ConvertToMatrixRep(vectorlist,F);
        ConvertToMatrixRep(vectorlistscalar,F);

        # Now put together the clean ones by our knowledge of c^-1:
        transr := [];
        CanonicalVC := BasisVectors(CanonicalBasis(VectorSpace(F,IdentityMat(aimdim-n,F))));
        for i in CanonicalVC do
            LinearCombinationVector := Coefficients(VCBasis,i);
            tf := IdentityMat(d,F);
            tfw := w.One;
            tfvalue := Zero(F);
            currentvector := Zero(VC);
            for lambda in [1..Size(LinearCombinationVector)] do
                if LinearCombinationVector[lambda] <> Zero(F) then
                    tfvalue := tfvalue + LinearCombinationVector[lambda]*(currentvector*vectorlistscalar[lambda]) + RECOG.ComputeCornerEntryProductSU(vectorlist[lambda], vectorlistscalar[lambda], diagonalentrylist[lambda], F,  Int(LinearCombinationVector[lambda]));
                    currentvector := currentvector + LinearCombinationVector[lambda]*vectorlist[lambda];
                    tfw := tfw*transw[lambda]^Int(LinearCombinationVector[lambda]);
                fi;
            od;
            tf[n,1] := -1*tfvalue;
            killerw := RECOG.WriteLowerKillerAsWordSU(tf{[1..n]}{[1..n]},n,d,w.One,w.transv1,w.transv2,w.sunstdf{[2*ext+1..(2*ext+ext/2)]},w.sunstdf[2*w.ext + (w.ext/2)+1],w.sunstdf[2*w.ext + (w.ext/2)+2],w.sunstdf[2*w.ext + (w.ext/2)+3],q,ext,alpha,p,phi);
            tfw := killerw*tfw;
            Add(transr,tfw);
        od;
        Unbind(trans);
        Unbind(transw);

        Info(InfoRecog,2,"Step 6 done");

        # From here on we distinguish three cases:
        #   * w.n = 2
        #   * we finish off the constructive recognition
        #   * we have to do another step as the next thing
        if n = 4 then
            #w.slnstdf[2*w.ext+2] := transd[1]*transr[1]^-1*transd[1];
            #w.slnstdf[2*w.ext+1] := w.transh[1]*w.transv[1]^-1*w.transh[1]
            #                        *w.slnstdf[2*w.ext+2];
            #Unbind(w.transh);
            #Unbind(w.transv);
            #w.n := 3;
            s := w.One;
            PermMat3 := PermutationMat((3,5)(6,4),d,F);
            v := w.sunstdf[2*w.ext+(w.ext/2)+1];
            #PermMat3 := PermutationMat((3,5)(6,4),20,GF(5));
            # w.ext = 2?
            #for i in [n-1,n-3..1] do
            flag := false;
            for i in [2] do
                if flag then
                    # Make [[0,-1],[1,0]] in coordinates w.n and w.n+i:
                    tf := transd[(i-1)*ext+1]*transr[i]^-1*transd[(i-1)*ext+1];
                else
                    # Make [[0,1],[-1,0]] in coordinates w.n and w.n+i:
                    #Display(transd[(i-1)*1+1]*transr[i]^-1*transd[(i-1)*1+1]);
                    tf := transd[(i-1)*ext+1]^-1*transr[i]*transd[(i-1)*ext+1]^-1;
                fi;
                #Display(tf);
                #Display((tf^(v^2))^(PermMat3^(-1)));
                s := s * tf;
                flag := not(flag);
            od;

            fixv := IdentityMat(d,F);
            fixv[1,1] := -1*One(F);
            fixv[4,4] := -1*One(F);

            v := v*s*w.sunstdf[2*w.ext+(w.ext/2)+4]^((Sqrt(q)-1)/2);
            #v := v*s;
            w.sunstdf[2*w.ext+(w.ext/2)+1] := v;

            newbasechange := PermMat3^(-1)*basechange;
            w.bas := PermMat3^(-1) * w.bas;
            w.basi := w.basi * PermMat3;
            
            # Now add the new transvections:
            # for i in [Size(transd)/2+1..Size(transd)] do
               # w.transh[w.ext*(w.n-1)+w.ext*(i-1)+1] := transr[i];
            #     Add(w.transh1, transd[i]^(-1));
            # od;
            # newtransv := transd{[1..Size(transd)/2]};
            # Append(newtransv,w.transh2);
            # Error("here");
            # w.transh2 := newtransv;
            w.n := aimdim;
            Info(InfoRecog,2,"Step 7 done");
            return w;
        fi;
        # We can finish off:

        if aimdim = w.GoalDim then
            # In this case we just finish off and do not bother with
            # the transvections, we will only need the standard gens:
            # Now put together the (newdim)-cycle:
            # n+newdim -> n+newdim-1 -> ... -> n+1 -> n -> n+newdim
            
            flag := false;
            s := w.One;
            PermMat3 := RECOG.ComputeCorrectingPermutationMat(d,F,n,aimdim);
            v := w.sunstdf[2*w.ext+(w.ext/2)+1];
            if newdim/2 = 1 then
                for i in [2] do
                    if flag then
                        # Make [[0,-1],[1,0]] in coordinates w.n and w.n+i:
                        tf := transd[(i-1)*ext+1]*transr[i]^-1*transd[(i-1)*ext+1];
                    else
                        # Make [[0,1],[-1,0]] in coordinates w.n and w.n+i:
                        tf := transd[(i-1)*ext+1]^-1*transr[i]*transd[(i-1)*ext+1]^-1;
                    fi;
                    s := s * tf;
                    flag := not(flag);
                od;

                # Finally put together the new long cycle:

                v := ((w.sunstdf[2*w.ext+(w.ext/2)+4]^((Sqrt(q)-1)/2))^((v*s*w.sunstdf[2*w.ext+(w.ext/2)+3])^(-1)))*(v*s);
                w.sunstdf[2*w.ext+(w.ext/2)+1] := v;
            else
                for i in Reversed([Size(transr)-(newdim/2)+1..Size(transr)]) do
                    if flag then
                        # Make [[0,-1],[1,0]] in coordinates w.n and w.n+i:
                        tf := transd[(i-1)*ext+1]*transr[i]^-1*transd[(i-1)*ext+1];
                    else
                        # Make [[0,1],[-1,0]] in coordinates w.n and w.n+i:
                        tf := transd[(i-1)*ext+1]^-1*transr[i]*transd[(i-1)*ext+1]^-1;
                    fi;
                    s := s * tf;
                    flag := not(flag);
                od;

                # Finally put together the new long cycle:
                if flag then
                    v := ((w.sunstdf[2*w.ext+(w.ext/2)+4]^((Sqrt(q)-1)/2))^((v*s*w.sunstdf[2*w.ext+(w.ext/2)+3])^(-1)))*(v*s);
                else
                    v := (v*s);
                fi;
                w.sunstdf[2*w.ext+(w.ext/2)+1] := v;
            fi;

            newbasechange := PermMat3^(-1)*basechange;
            w.bas := PermMat3^(-1) * w.bas;
            w.basi := w.basi * PermMat3;
            Unbind(w.transv);
            Unbind(w.transh);
            w.n := aimdim;
            Info(InfoRecog,2,"Step 7 done");
            return w;

        fi;

        # Otherwise we do want to go on as the next thing, so we want to
        # keep our transvections. This is easily done if we change the
        # basis one more time. Note that we know that n is odd here!

        # Put together the n-cycle:
        # 2n-1 -> 2n-2 -> ... -> n+1 -> n -> 2n-1
        flag := false;
        PermMat3 := RECOG.ComputeCorrectingPermutationMat(d,F,n,aimdim);
        s := w.One;
        v := w.sunstdf[2*w.ext+(w.ext/2)+1];
        for i in [n-2,n-3..(n/2)] do
            if flag then
                # Make [[0,-1],[1,0]] in coordinates w.n and w.n+i:
                # TODO: Replace 2 by size of extension to get the correct matrices of transd (we want the ones with 1 and -1 at the transvection positions)
                tf := transd[(i-1)*ext+1]*transr[i]^-1*transd[(i-1)*ext+1];
            else
                # Make [[0,1],[-1,0]] in coordinates w.n and w.n+i:
                # TODO: Replace 2 by size of extension to get the correct matrices of transd (we want the ones with 1 and -1 at the transvection positions)
                tf := transd[(i-1)*ext+1]^-1*transr[i]*transd[(i-1)*ext+1]^-1;
            fi;
            s := s * tf;
            flag := not(flag);
        od;

        # Finally put together the new long cycle:
        v := (v*s);
        w.sunstdf[2*w.ext+(w.ext/2)+1] := v;

        newbasechange := PermMat3^(-1)*basechange;
        w.bas := PermMat3^(-1) * w.bas;
        w.basi := w.basi * PermMat3;

        w.n := aimdim;

        Info(InfoRecog,2,"Step 7 done");
        return w;
    fi;
end;
