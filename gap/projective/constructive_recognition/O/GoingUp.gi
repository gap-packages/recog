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
######## GoingUp method for orthogonal groups ###############################
#############################################################################
#############################################################################



# change input into H again
RECOG.Omegan_UpStep := function(H,G,n,basechange)
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
local d, id, FixSpn, Vn, q, p, F, t, GM, counter, aimdim, newdim, c1, c, ci, sum1, int1, i, v1, v2, v3, L1, L2, newpart, zerovec, MB, newbas, newbasi, int3, pivots, cii, pivots2, 
      newbasechange, trans, tf, lambda, killer, transr, gamma1, gamma2, gamma3, gamma4, gamma0, zeta, k, beta, vectorw, normx, PermMat, PermMat2, HBig, HBigGens, H2n, HSmall, transd,
      WrongForm, ChangeToCorrectForm, ChangeToCorrectFormBig, extract, ChangeToCorrectForm2, ChangeToCorrectFormBig2, FormValue, killervalue, killersupport, vectorlist, VC, VCBasis, HFake,
      LinearCombinationVector, s, flag, v, PermMat3, fixv, factors, ext, vectorlistindex, vectorlist2, vectorlistele, indexlist, VCBuildBasis, CanonicalVC,form, 
      ChangeToCorrectFormBig22, ciT, basechangeBackUp;

    F := FieldOfMatrixGroup(H);
    d := Size(GeneratorsOfGroup(G)[1]);
    q := Size(F);
    factors := Factors(q);
    p := Factors(q)[1];
    ext := Size(factors);

    # Here everything starts, some more preparations:

    # We compute exclusively in our basis, so we occasionally need an
    # identity matrix:
    id := IdentityMat(d,F);
    FixSpn := VectorSpace(F,id{[n+1..d]});
    Vn := VectorSpace(F,id{[1..n]});

    Info(InfoRecog,2,"Current dimension: " );
    Info(InfoRecog,2,n);
    Info(InfoRecog,2,"\n");
    Info(InfoRecog,2,"New dimension: ");
    Info(InfoRecog,2,Minimum(2*n-4,d));
    Info(InfoRecog,2,"\n");
    #aimdim := Minimum(2*n-2,d);
    #newdim := aimdim - n;
    aimdim := Minimum(2*n-4,d);
    newdim := aimdim - n;
    form := PreservedSesquilinearForms(Omega(1,n,q))[1]!.matrix;
    counter := 0;
    basechangeBackUp := MutableCopyMat(basechange);

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
        t := PermutationMat((2,3)(4,5),d,F);
    fi;

    if n > 6 then 
        v := Zero(F) * IdentityMat( n, F );
        v[n/2][1] := One(F);
        v{[1..(n/2)-1]}{[2..n/2]} := IdentityMat((n/2)-1,F);
        v[n/2+1][n] := One(F);
        v{[(n/2)+2..n]}{[(n/2)+1..n-1]} := IdentityMat((n/2)-1,F);
        t{[1..n]}{[1..n]} := v;
        t := PermutationMat((2,3,4)(5,7,6),d,F);
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
            c1 := c1^((basechange)^(-1));
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

                if v1{[1..n]}*form*v1{[1..n]} = Zero(F) and v2{[1..n]}*form*v2{[1..n]} = Zero(F) then

                    L1 := IdentityMat(d,F);
                    L2 := IdentityMat(d,F);

                    for i in [2..n-1] do
                        L1[1,i] := v1[i];
                        L1[n-i+1,n] := -1*v1[i];
                    od;
                    if v1[n] <> Zero(F) then
                        L1[1,n] := v1[n];
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

                    v2 := v2 / v2[n];   # normalize to 1 in position n
                    Assert(1,v2*c=v2);

                    if v2{[1..n]}*form*v2{[1..n]} = Zero(F) then

                        for i in [2..n-1] do
                            L2[n,i] := v2[i];
                            L2[n-i+1,1] := -1*v2[i];
                        od;
                        if v2[1] <> Zero(F) then
                            L2[n,1] := v2[1];
                        fi;

                        c := L2*c*L2^(-1);
                        ci := c^-1;
                        break;
                    fi;
                    Display("fail");
                fi;
                Display("fail");
            fi;
            # Display(counter);
        od;
        
        Info(InfoRecog,2,"Step 2 done.");

        # Now we found our aimdim-dimensional space W. Since Sp_n
        # has a d-n-dimensional fixed space W_{d-n} and W contains a complement
        # of that fixed space, the intersection of W and W_{d-n} has dimension
        # newdim.

        # Change basis:
        newpart := ExtractSubMatrix(c,[2..(n-1)],[1..(d)]);
        # Clean out the first n entries to go to the fixed space of Sp_n:
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

            Info(InfoRecog,2,"Start of form change");

            # Transform the form into standard form

            # TODO: Base change not completely correct yet
            HFake := RECOG.LiftGroup(GeneratorsOfGroup(Omega(1,n,q)),n,q,d)[1];
            HBigGens := List(GeneratorsOfGroup(HFake),MutableCopyMat);
            Append(HBigGens,GeneratorsOfGroup(HFake^c));
            HBig := GroupByGenerators(HBigGens);
            basechange := newbasechange;
            HSmall := GroupByGenerators(List(GeneratorsOfGroup(HBig),x->x{[1..aimdim]}{[1..aimdim]}));
            WrongForm := PreservedSesquilinearForms(HSmall)[1];
            FormValue := (WrongForm!.matrix)[1,n];
            extract := BilinearFormByMatrix((FormValue^(-1)*WrongForm!.matrix){[n+1..aimdim]}{[n+1..aimdim]}, F );
            ChangeToCorrectForm := BaseChangeToCanonical(extract);
            ChangeToCorrectFormBig := IdentityMat(aimdim,F);
            ChangeToCorrectFormBig{[n+1..aimdim]}{[n+1..aimdim]} := ChangeToCorrectForm;
            ChangeToCorrectFormBig2 := IdentityMat(d,F);
            ChangeToCorrectFormBig2{[1..aimdim]}{[1..aimdim]} := ChangeToCorrectFormBig^(-1);
            HBig := HBig^ChangeToCorrectFormBig2;
            c := ChangeToCorrectFormBig2^(-1) * c * ChangeToCorrectFormBig2;
            basechange := ChangeToCorrectFormBig2^(-1)*basechange;

            if aimdim - n > 2 then
                # TODO: Adjust next line to omega groups
                ChangeToCorrectFormBig22 := RECOG.ComputeCorrectingPermutationMatSpTwo(d,F,n,aimdim);
                HBig := HBig^ChangeToCorrectFormBig22;
                c := ChangeToCorrectFormBig22^(-1) * c * ChangeToCorrectFormBig22;
                basechange := ChangeToCorrectFormBig22^(-1)*basechange;
            fi;

            # TODO: Try hack
            HFake := RECOG.LiftGroup(GeneratorsOfGroup(Omega(1,n,q)),n,q,d)[1];
            HBigGens := List(GeneratorsOfGroup(HFake),MutableCopyMat);
            Append(HBigGens,GeneratorsOfGroup(HFake^c));
            HBig := GroupByGenerators(HBigGens);
            HSmall := GroupByGenerators(List(GeneratorsOfGroup(HBig),x->x{[1..aimdim]}{[1..aimdim]}));
            WrongForm := PreservedSesquilinearForms(HSmall)[1];
            FormValue := (WrongForm!.matrix)[1,n];
            extract := BilinearFormByMatrix((FormValue^(-1)*WrongForm!.matrix){[n+1..aimdim]}{[n+1..aimdim]}, F );

            if (extract!.matrix)[1,1] = Zero(F) then
                ChangeToCorrectForm := BaseChangeToCanonical(extract);
                ChangeToCorrectFormBig := IdentityMat(aimdim,F);
                ChangeToCorrectFormBig{[n+1..aimdim]}{[n+1..aimdim]} := ChangeToCorrectForm;
                ChangeToCorrectFormBig2 := IdentityMat(d,F);
                ChangeToCorrectFormBig2{[1..aimdim]}{[1..aimdim]} := ChangeToCorrectFormBig^(-1);
                HBig := HBig^ChangeToCorrectFormBig2;
                c := ChangeToCorrectFormBig2^(-1) * c * ChangeToCorrectFormBig2;
                basechange := ChangeToCorrectFormBig2^(-1)*basechange;

                if aimdim - n > 2 then
                    # TODO: Adjust next line to omega groups
                    ChangeToCorrectFormBig22 := RECOG.ComputeCorrectingPermutationMatSpTwo(d,F,n,aimdim);
                    HBig := HBig^ChangeToCorrectFormBig22;
                    c := ChangeToCorrectFormBig22^(-1) * c * ChangeToCorrectFormBig22;
                    basechange := ChangeToCorrectFormBig22^(-1)*basechange;
                fi;

                ci := c^-1;
                ciT := TransposedMat(ci);

                Info(InfoRecog,2,"End of form change");

                break;
            else
                Info(InfoRecog,2,"End of form change");
                basechange := basechangeBackUp;
            fi;
        fi;
        Info(InfoRecog,2,"Ooops, no nice bottom or the wrong orhtogonal group...");
        # Otherwise simply try again
    od;


     # Now consider the transvections t_i:
    # t_i : w.bas[j] -> w.bas[j]        for j <> i and
    # t_i : w.bas[i] -> w.bas[i] + ww
    # We want to modify (t_i)^c such that it fixes w.bas{[1..w.n]}:
    if not(IsEvenInt(aimdim)) then
        trans := [];
        vectorlist := [];
        for i in [1..(n-2)] do
            # This does t_i
            for lambda in [One(F)] do
                # This does t_i : v_j -> v_j + lambda * v_n
                tf := IdentityMat(d,F);
                tf[i+1,n] := lambda;
                tf[1,n-i] := -1*(lambda);
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
                    killersupport[n-killervalue+1,n] := (tf[1,killervalue]);
                    #Display(killersupport);
                    killer := killer*killersupport;
                od;
                #killer{[1..n]}{[1..n]} := tf{[1..n]}{[1..n]}^(-1);
                #if (killer^newbasechange)^testchange in SO(1,d,q) then
                #    tf := killer*tf;
                #else
                #    Error("this should not happen.");
                #fi;
                Add(vectorlist,tf{[n+1..aimdim]}{[n]});
                Add(trans,tf);
            od;
        od;

        # For now vector space variant. but change that!
        VC := VectorSpace(GF(p),vectorlist);

        # If we are finishing up, then we have to take a linear independent subset
        if aimdim < 2*n-4 then
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
                #if killer^newbasechange in G then
                #    tf := killer*tf;
                #else
                #    Error("this should not happen.");
                #fi;
            fi;
            Add(transd,tf);
        od;
        Unbind(trans);

        Info(InfoRecog,2,"Step 5 done");

        # Now to the "horizontal" transvections, first create them as SLPs:
        transr := [];
        trans := [];
        vectorlist := [];
        for lambda in [One(F)] do
            # This does t_i
            for i in [2..(n-1)] do
                # This does t_i : v_j -> v_j + lambda * v_n
                tf := IdentityMat(d,F);
                tf[i,1] := lambda;
                tf[n,n-i+1] := -1*(lambda);
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
                    killersupport[n,n-killervalue+1] := (tf[killervalue,1]);
                    #Display(killersupport);
                    killer := killer*killersupport;
                od;
                #killer{[1..n]}{[1..n]} := tf{[1..n]}{[1..n]}^(-1);
                #if killer^newbasechange in G then
                #    tf := killer*tf;
                #else
                #    Error("this should not happen.");
                #fi;
                Add(vectorlist,tf{[n]}{[n+1..aimdim]});
                Add(trans,tf);
            od;
        od;

        # For now vector space variant. but change that!
        VC := VectorSpace(GF(p),vectorlist);
        if aimdim < 2*n-4 then
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
                #if killer^newbasechange in G then
                #    tf := killer*tf;
                #else
                #    Error("this should not happen.");
                #fi;
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
            for lambda in [One(F)] do
                # This does t_i : v_j -> v_j + lambda * v_n
                tf := IdentityMat(d,F);
                tf[i+1,n] := lambda;
                tf[1,n-i] := -1*(lambda);
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
                    killersupport[n-killervalue+1,n] := (tf[1,killervalue]);
                    #Display(killersupport);
                    killer := killer*killersupport;
                od;
                #killer{[1..n]}{[1..n]} := tf{[1..n]}{[1..n]}^(-1);
                if killer{[1..n]}{[1..n]} in Omega(1,n,q) then
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
                tf := tf*trans[indexlist[lambda]]^Int(LinearCombinationVector[lambda]);
            od;
            killer{[1..n]}{[1..n]} := tf{[1..n]}{[1..n]}^(-1);
            if RECOG.IsInOmega(Omega(1,d,q),killer^basechange) then
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
        for lambda in [One(F)] do
            # This does t_i
            for i in [2..(n-1)] do
                # This does t_i : v_j -> v_j + lambda * v_n
                tf := IdentityMat(d,F);
                tf[i,1] := lambda;
                tf[n,n-i+1] := -1*(lambda);
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
                    killersupport[n,n-killervalue+1] := (tf[killervalue,1]);
                    #Display(killersupport);
                    killer := killer*killersupport;
                od;
                #killer{[1..n]}{[1..n]} := tf{[1..n]}{[1..n]}^(-1);
                if killer{[1..n]}{[1..n]} in Omega(1,n,q) then
                    tf := killer*tf;
                else
                    Error("this should not happen.");
                fi;
                Add(vectorlist,tf{[n]}{[n+1..aimdim]});
                Add(trans,tf);
            od;
        od;

        # For now vector space variant. but change that!
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

        for i in BasisVectors(CanonicalBasis(VectorSpace(F,IdentityMat(n-4,F)))) do
            LinearCombinationVector := Coefficients(VCBasis,[i]);
            tf := IdentityMat(d,F);
            for lambda in [1..Size(LinearCombinationVector)] do
                tf := tf*trans[indexlist[lambda]]^Int(LinearCombinationVector[lambda]);
            od;
            killer{[1..n]}{[1..n]} := tf{[1..n]}{[1..n]}^(-1);
            if killer{[1..n]}{[1..n]} in Omega(1,n,q) then
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
        if n = 6 then
            #w.slnstdf[2*w.ext+2] := transd[1]*transr[1]^-1*transd[1];
            #w.slnstdf[2*w.ext+1] := w.transh[1]*w.transv[1]^-1*w.transh[1]
            #                        *w.slnstdf[2*w.ext+2];
            #Unbind(w.transh);
            #Unbind(w.transv);
            #w.n := 3;
            flag := false;
            s := IdentityMat(d,F);
            PermMat3 := PermutationMat((4,7,5,8,6),d,F);
            v := PermutationMat((1,2,3)(4,6,5),d,F);
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

            # Now compute v*s
            fixv := IdentityMat(d,F);
            fixv[1,1] := -1*One(F);
            fixv[6,6] := -1*One(F);
            newbasechange := PermMat3*basechange;
            Display((v*s*fixv)^(PermMat3^(-1)));
            Info(InfoRecog,2,"Step 7 done");
            return newbasechange;
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
        PermMat3 := PermutationMat((5,9)(6,10)(7,11)(8,12),d,F);
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
        for i in [n-4,n-5..((n/2)-1)] do
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
            Display(tf);
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



RECOG.TestSpaceForSingularPoints := function(U,form,F)
local v, w1, w2;

    w1 := Zero(U);
    w2 := Zero(U);

    for v in U do
        if w1 = Zero(U) then
            if v*form*v = Zero(F) then
                w1 := v;
            fi;
        else
            if v*form*v = Zero(F) and not(v in VectorSpace(F,[w1])) then
                w2 := v;
                return true;
            fi;
        fi;
    od;

    return false;

end;


RECOG.TestOmega4DimensionalSpace := function(d,q,type,tries)
local V, G, form, i, j, gens, v;

    G := Omega(type,d,q);
    form := (PreservedSesquilinearForms(G)[1])!.matrix;
    V := VectorSpace(GF(q),IdentityMat(d,GF(q)));
    
    i := 1;
    while i < tries do
        gens := [];
        while Size(gens) < 4 do
            v := PseudoRandom(V);
            if Size(gens) = 0 then
                gens := [v];
            else
                if not(v in VectorSpace(GF(q),gens)) then
                    Add(gens,v);
                fi;
            fi;
        od;
        Display(RECOG.TestSpaceForSingularPoints(VectorSpace(GF(q),gens), form, GF(q)));
        gens := [];
        i := i + 1;
    od;

end;