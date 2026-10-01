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
######## GoingUp method for symplectic groups ###############################
#############################################################################
#############################################################################



RECOG.ComputeCorrectingPermutationMatSp:= function(d,F,n,aimdim)
local list, half;

    list := Concatenation([n+1..aimdim],[(n/2)+1..n]);

    return PermutationMat(MappingPermListList([(n/2)+1..aimdim],list)^(-1),d,F);

end;



RECOG.ComputeCorrectingPermutationMatSpTwo:= function(d,F,n,aimdim)
local list, list1, list2, mat, more;

    mat := IdentityMat(d,F);
    more := aimdim - n;
    list1 := [1..more];
    list2 := Reversed(Filtered(list1,x->IsEvenInt(x)));
    list1 := Filtered(list1,x->IsOddInt(x));
    list := Concatenation(list1,list2);

    mat{[n+1..aimdim]}{[n+1..aimdim]} := PermutationMat(MappingPermListList([1..more],list)^(-1),more,F);
    return mat;

end;



RECOG.SymplecticGroupStandardGenerators := function(d,n,q,f,F)
local s,u,v,diag,upper,lower, gens, list1, list2, ele, omega, i, one;

    gens := [3*f+4];
    upper := [1..f];
    lower := [1..f];
    diag := [1..f];

    s := PermutationMat((1,n),d,F);
    s[n,1] := -1*One(F);
    ConvertToMatrixRepNC(s,F);
    
    u := PermutationMat((1,2)(n-1,n),d,F);
    ConvertToMatrixRepNC(u,F);

    list1 := [1..n/2];
    list2 := Reversed([n/2+1..n]);
    v := PermutationMat(CycleFromList(list1)*CycleFromList(list2),d,F);
    ConvertToMatrixRepNC(v,F);

    omega := PrimitiveElement(F);
    one := IdentityMat(d,F);
    for i in [1..f] do
        ele := MutableCopyMat(one);
        ele[1,2] := omega^(i-1);
        ele[n-1,n] := -1*omega^(i-1);
        ConvertToMatrixRepNC(ele,F);
        upper[i] := ele;
        ele := MutableCopyMat(one);
        ele[2,1] := omega^(i-1);
        ele[n,n-1] := -1*omega^(i-1);
        ConvertToMatrixRepNC(ele,F);
        lower[i] := ele;
        ele := MutableCopyMat(one);
        ele[1,n] := omega^(i-1);
        ConvertToMatrixRepNC(ele,F);
        diag[i] := ele;
    od;

    ele := MutableCopyMat(one);
    ele[1,1] := omega;
    ele[n,n] := omega^(-1);

    gens{[1..f]} := upper;
    gens{[f+1..2*f]} := lower;
    gens{[2*f+1..3*f]} := diag;
    gens[3*f+1] := v;
    gens[3*f+2] := u;
    gens[3*f+3] := s;
    gens[3*f+4] := ele;

    return gens;
end;



RECOG.WriteLAsWord := function(L,n,d,onef,spnstdf,q,f,bool)
local tf, value, i, j, omega, basis, coeffs, coeff, trans, diag, s, v, u, shift, one, t, turn;

    #one := IdentityMat(n,GF(q));
    if bool then
        trans := spnstdf{[1..f]};
    else
        trans := spnstdf{[f+1..2*f]};
    fi;

    v := spnstdf[3*f+1];
    u := spnstdf[3*f+2];
    s := spnstdf[3*f+3];
    shift := v*u;

    diag := spnstdf{[2*f+1..3*f]};

    omega := PrimitiveElement(GF(q));
    basis := [1..f];
    for i in [0..f-1] do
        basis[i+1] := omega^i;
    od;
    basis := Basis(GF(q),basis);

    for i in [2..(n/2)] do
        if bool then
            value := L[1,i];
        else
            value := L[i,1];
        fi;
        coeffs := Coefficients(basis,value);
        for j in [1..f] do
            coeff := Int(coeffs[j]);
            onef := onef * trans[j]^coeff;
        od;
        trans := List(trans,x->x^shift);
        #t := IdentityMat(n,GF(q));
        #if bool then
        #    t[1,i] := value;
        #    t[n-i+1,n] := -1*value;
        #else
        #    t[i,1] := value;
        #    t[n,n-i+1] := -1*value;
        #fi;
        #one := one*t;
    od;

    if bool then
        trans := spnstdf{[f+1..2*f]};
    else
        trans := spnstdf{[1..f]};
    fi;

    trans := List(trans,x->x^(shift^((n/2)-2)));
    trans := List(trans,x->x^s);

    for i in [(n/2)+1..n-1] do
        if bool then
            value := L[1,i];
        else
            value := L[i,1];
        fi;
        coeffs := Coefficients(basis,value);
        for j in [1..f] do
            coeff := Int(coeffs[j]);
            onef := onef * trans[j]^coeff;
        od;
        trans := List(trans,x->x^(shift^(-1)));
        #t := IdentityMat(n,GF(q));
        #if bool then
        #    t[1,i] := value;
        #    t[n-i+1,n] := value;
        #else
        #    t[i,1] := value;
        #    t[n,n-i+1] := value;
        #fi;
        #one := one*t;
    od;

    if bool then
        value := RECOG.ComputeCornerEntry((L{[1]}{[2..n-1]})[1],n-2,GF(q));
        #value := one[1,n];
        coeffs := Coefficients(basis,-1*value);
        for j in [1..f] do
            coeff := Int(coeffs[j]);
            onef := onef * diag[j]^coeff;
        od;
    else
        #value := one[n,1];
        value := -1*RECOG.ComputeCornerEntry((L{[1]}{[2..n-1]})[1],n-2,GF(q));
        coeffs := Coefficients(basis,value);
        turn := diag[1]^0;
        for j in [1..f] do
            coeff := Int(coeffs[j]);
            turn := turn * diag[j]^coeff;
        od;
        turn := turn^s;
        onef := onef*turn;
    fi;

    return onef;

end;



RECOG.WriteUpperKillerAsWord := function(L,n,d,onef,trans1,trans2,diag,v,u,s,q,f)
local tf, value, i, j, omega, basis, coeffs, coeff, trans, shift, one, t, turn;

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

    value := L[1,n]-RECOG.ComputeCornerEntry((L{[1]}{[2..n-1]})[1],n-2,GF(q));
    #value := L[1,n]-one[1,n];
    coeffs := Coefficients(basis,value);
    for j in [1..f] do
        coeff := Int(coeffs[j]);
        onef := onef * diag[j]^coeff;
    od;

    return onef;

end;



RECOG.WriteLowerKillerAsWord := function(L,n,d,onef,trans1,trans2,diag,v,u,s,q,f)
local tf, value, i, j, omega, basis, coeffs, coeff, trans, shift, one, t, turn;

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

    value := -1*(L[n,1]-(-1*RECOG.ComputeCornerEntry((TransposedMat(L){[1]}{[2..n-1]})[1],n-2,GF(q)))); 
    #value := -1*(L[n,1]-one[n,1]);
    coeffs := Coefficients(basis,value);
    turn := diag[1]^0;
    for j in [1..f] do
        coeff := Int(coeffs[j]);
        turn := turn * diag[j]^coeff;
    od;
    turn := turn^s;
    onef := onef*turn;

    return onef;

end;



RECOG.ComputeCornerEntry := function(list, length, F)
local value, i;

    value := Zero(F);
    for i in [1..length/2] do
        value := value + list[i] * list[length-i+1];
    od;

    return value;

end;



# change input into H again
RECOG.Spn_UpStep := function(w)
# w has components:
#   d       : size of big Sp
#   n       : size of small Sp
#   spnstdf : fakegens for Sp_n standard generators
#   bas     : current base change, first n vectors are where Sp_n acts
#             rest of vecs are invariant under Sp_n
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
#   transh  : fakegens for the "horizontal" transvections n,i for 1<=i<=n/2
#             entries can be unbound in which case they are made from spnstdf
#   transv  : fakegens for the "vertical" transvections i,n for 1<=i<=n/2
#             entries can be unbound in which case they are made from spnstdf
#
# We keep the following invariants (going from n -> n':=2n-2)
#   bas, basi is a base change to the target base
#   spnstdf are SLPs to reach standard generators of Sp_n from the
#       generators of sld
local d, id, q, F, t, GM, counter, aimdim, newdim, c1, c, ci, sum1, int1, i, v1, v2, L1, L2, newpart, zerovec, MB, newbas, newbasi, factors, ext, HBig,
int3, pivots, cii, pivots2, newbasechange, trans, tf, tw, lambda, killer, transr, vectorlist, VC, CanonicalVC, LinearCombinationVector, transd, vectorlist2, indexlist, 
p, VCBuildBasis, vectorlistele, VCBasis, vectorlistindex, flag, v, s, PermMat3, PermMat, PermMat2, ChangeToCorrectForm, ChangeToCorrectFormBig2, ChangeToCorrectFormBig22,
ChangeToCorrectForm2, ChangeToCorrectFormBig, WrongForm, FormValue, HSmall, extract, HBigGens, WrongForm2, H, G, n, basechange, L1w, L2w, initele, pos, k, shift, pos2, tfw, tfvalue, vectorlistscalar, currentvector,
slp, c1w, cw, cwi, HFake, HBigF, FakeBigGens, SuperFake, killerw, transw, newtransv, begintransv, difftransv, ciT;

    Info(InfoRecog,3,"Going up: ",w.n," (",w.d,")...");

    # Before we begin, we upgrade the data structure with a few internal
    # things:

    if not(IsBound(w.can)) then w.can := CanonicalBasis(w.f); fi;
    if not(IsBound(w.canb)) then w.canb := BasisVectors(w.can); fi;
    if not(IsBound(w.One)) then w.One := One(w.spnstdf[1]); fi;
    if not(IsBound(w.transh1)) then w.transh1 := []; fi;
    if not(IsBound(w.transv1)) then w.transv1 := []; fi;
    w.transv2 := [];
    w.transh2 := [];

    for k in [1..w.ext] do
        pos := k;
        if not(IsBound(w.transh1[pos])) then
            w.transh1[pos] := w.spnstdf[k];
        fi;
        if not(IsBound(w.transv1[pos])) then
            w.transv1[pos] := w.spnstdf[w.ext + k];
        fi;
    od;

    shift := w.spnstdf[3*w.ext + 1] * w.spnstdf[3*w.ext + 2];
    for i in [3..(w.n)/2] do
        for k in [1..w.ext] do
            pos := (i-2)*w.ext + k;
            if not(IsBound(w.transh1[pos])) then
                # TODO: Remove initele
                initele := One(w.spnstdf[1]);
                initele := (initele * w.transh1[pos-w.ext])^shift;
                w.transh1[pos] := initele;
            fi;
            if not(IsBound(w.transv1[pos])) then
                # TODO: Remove initele
                initele := One(w.spnstdf[1]);
                initele := (initele * w.transv1[pos-w.ext])^shift;
                w.transv1[pos] := initele;
            fi;
        od;
    od;

    for k in [1..w.ext] do
        pos := k;
        pos2 := ((w.n)/2-2)*w.ext+k;
        if not(IsBound(w.transv2[pos])) then
            initele := One(w.spnstdf[1]);
            initele := (initele * w.transh1[pos2])^w.spnstdf[3*w.ext + 3];
            w.transv2[pos] := initele;
        fi;
        if not(IsBound(w.transh2[pos])) then
            initele := One(w.spnstdf[1]);
            initele := (initele * w.transv1[pos2])^w.spnstdf[3*w.ext + 3];
            w.transh2[pos] := initele;
        fi;
    od;

    shift := shift^(-1);
    for i in [3..(w.n)/2] do
        for k in [1..w.ext] do
            pos := (i-2)*w.ext + k;
            if not(IsBound(w.transh2[pos])) then
                initele := One(w.spnstdf[1]);
                initele := (initele * w.transh2[pos-w.ext])^shift;
                w.transh2[pos] := initele;
            fi;
            if not(IsBound(w.transv2[pos])) then
                initele := One(w.spnstdf[1]);
                initele := (initele * w.transv2[pos-w.ext])^shift;
                w.transv2[pos] := initele;
            fi;
        od;
    od;

    H := GroupByGenerators(w.spnstdf);
    G := w.sld;
    n := w.n;
    basechange := w.bas;

    d := w.d;
    p := w.p;
    ext := w.ext;
    q := p^ext;
    F := GF(q);

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
        tw := w.spnstdf[3*w.ext+1];
    fi;

    Info(InfoRecog,2,"Step 1 done.");

    # Find a good random element:
    w.count := 0;
    aimdim := Minimum(2*n-2,d);
    newdim := aimdim - n;
    counter := 0;
    while true do   # will be left by break
        while true do    # will be left by break
            counter := counter + 1;
            w.count := w.count + 1;
            if InfoLevel(InfoRecog) >= 3 then Print(".\c"); fi;
            c1 := PseudoRandom(G);
            
            # Do the base change into our basis:
            c := t^(w.bas * c1 * w.basi);
            
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

                v1 := v1 / v1[1];   # normalize to 1 in position n
                Assert(1,v1*c=v1);

                L1 := IdentityMat(d,F);
                L2 := IdentityMat(d,F);

                for i in [2..n-1] do
                    L1[1,i] := v1[i];
                    if i <= n/2 then
                        L1[n-i+1,n] := -1*v1[i];
                    else
                        L1[n-i+1,n] := v1[i];
                    fi;
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

                for i in [2..n-1] do
                    L2[n,i] := v2[i];
                    if i <= n/2 then
                        L2[n-i+1,1] := v2[i];
                    else
                        L2[n-i+1,1] := -1*v2[i];
                    fi;
                od;
                if v2[1] <> Zero(F) then
                    L2[n,1] := v2[1];
                fi;

                c := L2*c*L2^(-1);
                ci := c^-1;

                break;
            fi;
        od;

        # We have to write L1 and L2 as words in spnstdf
        L1w := RECOG.WriteLAsWord(L1,n,d,w.One,w.spnstdf,q,ext,true);
        L2w := RECOG.WriteLAsWord(L2,n,d,w.One,w.spnstdf,q,ext,false);

        # Save the SLP for c
        slp := SLPOfElm(c1);
        c1w := ResultOfStraightLineProgram(slp,w.sldf);
        cw := tw^c1w;
        cw := L1w*cw*L1w^(-1);
        cw := L2w*cw*L2w^(-1);
        cwi := cw^-1;
        
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
            w.bas := newbas * w.bas;
            w.basi := w.basi * newbasi;
            break;
        fi;
        Info(InfoRecog,2,"Ooops, no nice bottom...");
        # Otherwise simply try again
    od;

    Info(InfoRecog,2,"Begin with form change");

    # Transform the form into standard form
    HFake := RECOG.LiftGroup(GeneratorsOfGroup(Sp(n,q)),n,q,d)[1];
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
    w.bas := ChangeToCorrectFormBig2^(-1) * w.bas;
    w.basi := w.basi * ChangeToCorrectFormBig2;

    if aimdim - n > 2 then
        ChangeToCorrectFormBig22 := RECOG.ComputeCorrectingPermutationMatSpTwo(d,F,n,aimdim);
        HBig := HBig^ChangeToCorrectFormBig22;
        c := ChangeToCorrectFormBig22^(-1) * c * ChangeToCorrectFormBig22;
        basechange := ChangeToCorrectFormBig22^(-1)*basechange;
        w.bas := ChangeToCorrectFormBig22^(-1) * w.bas;
        w.basi := w.basi * ChangeToCorrectFormBig22;
    fi;

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

    for i in pivots2 do
        for lambda in w.canb do
            tf := IdentityMat(d,F);
            tf{[2..n-1]}{[n]} := lambda * ci{[2..n-1]}{[i+1]};
            if i+1 <= n/2 then
                tfw := w.One*w.transh2[Size(w.transh2)-(i*w.ext)+Position(w.canb,lambda)];
                tf{[1]}{[2..n-1]} := lambda * c{[n-i]}{[2..n-1]};
                Add(vectorlistscalar,lambda * c[n-i]{[n+1..aimdim]});
            else
                tfw := (w.One*w.transh1[Size(w.transh1)-((i-n/2+1)*w.ext)+Position(w.canb,lambda)])^(-1);
                tf{[1]}{[2..n-1]} := -1 * lambda * c{[n-i]}{[2..n-1]};
                Add(vectorlistscalar,-1*lambda * c[n-i]{[n+1..aimdim]});
            fi;

            # Now conjugate with c:
            tfw := cwi*tfw*cw;

            # Now cleanup in column n above row n, the entries there
            killerw := RECOG.WriteUpperKillerAsWord(tf{[1..n]}{[1..n]}^(-1),n,d,w.One,w.transh1,w.transh2,w.spnstdf{[2*ext+1..3*ext]},w.spnstdf[3*ext+1],w.spnstdf[3*ext+2],w.spnstdf[3*ext+3],q,ext);
            tfw := killerw*tfw;
            Add(vectorlist, lambda * ciT[i+1]{[n+1..aimdim]});
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
            tfvalue := tfvalue + LinearCombinationVector[lambda]*(currentvector*vectorlist[lambda]);
            currentvector := currentvector + LinearCombinationVector[lambda]*vectorlistscalar[lambda];
            tfw := tfw*transw[lambda]^Int(LinearCombinationVector[lambda]);
        od;
        tf[1,n] := tfvalue;
        killerw := RECOG.WriteUpperKillerAsWord(tf{[1..n]}{[1..n]}^(-1),n,d,w.One,w.transh1,w.transh2,w.spnstdf{[2*ext+1..3*ext]},w.spnstdf[3*ext+1],w.spnstdf[3*ext+2],w.spnstdf[3*ext+3],q,ext);
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
    lambda := One(F);
    
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
            tf := IdentityMat(d,F);
            tf{[n]}{[2..n-1]} := lambda * c{[i+1]}{[2..n-1]};
            if i+1 <= n/2 then
                tfw := w.One*w.transv2[Size(w.transv2)-(i*w.ext)+Position(w.canb,lambda)];
                tf{[2..n-1]}{[1]} := lambda * ci{[2..n-1]}{[n-i]};
                Add(vectorlistscalar,lambda * ciT[n-i]{[n+1..aimdim]});
            else
                tfw := (w.One*w.transv1[Size(w.transv1)-((i-n/2+1)*w.ext)+Position(w.canb,lambda)])^(-1);
                tf[n-i,1] := -1*lambda;
                tf{[2..n-1]}{[1]} := -1*lambda * ci{[2..n-1]}{[n-i]};
                Add(vectorlistscalar, -1 * lambda * ciT[n-i]{[n+1..aimdim]});
            fi;

            # Now conjugate with c:
            tfw := cwi*tfw*cw;

            killerw := RECOG.WriteLowerKillerAsWord(tf{[1..n]}{[1..n]}^(-1),n,d,w.One,w.transv1,w.transv2,w.spnstdf{[2*ext+1..3*ext]},w.spnstdf[3*ext+1],w.spnstdf[3*ext+2],w.spnstdf[3*ext+3],q,ext);
            tfw := killerw*tfw;
            Add(trans,tf);
            Add(transw,tfw);
            Add(vectorlist, lambda * c[i+1]{[n+1..aimdim]});
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
        tfvalue := Zero(F);
        tfw := w.One;
        tfvalue := Zero(F);
        currentvector := Zero(VC);
        for lambda in [1..Size(LinearCombinationVector)] do
            tfvalue := tfvalue + LinearCombinationVector[lambda]*(currentvector*vectorlist[lambda]);
            currentvector := currentvector + LinearCombinationVector[lambda]*vectorlistscalar[lambda];
            tfw := tfw*transw[lambda]^Int(LinearCombinationVector[lambda]);
        od;
        tf[n,1] := -1*tfvalue;
        killerw := RECOG.WriteLowerKillerAsWord(tf{[1..n]}{[1..n]}^(-1),n,d,w.One,w.transv1,w.transv2,w.spnstdf{[2*ext+1..3*ext]},w.spnstdf[3*ext+1],w.spnstdf[3*ext+2],w.spnstdf[3*ext+3],q,ext);
        tfw := killerw*tfw;
        Add(transr,tfw);
    od;
    Unbind(trans);
    Unbind(transw);

    Info(InfoRecog,2,"Step 6 done");

    # From here on we distinguish three cases:
    #  * w.n = 4
    #  * we finish off the constructive recognition
    #  * we have to do another step as the next thing
    if w.n = 4 then
        flag := false;
        s := w.One;
        PermMat3 := RECOG.ComputeCorrectingPermutationMatSp(d,F,n,aimdim);
        v := w.spnstdf[3*ext+1];
        for i in [n-2,n-3..(n/2)] do
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
        v := ((w.spnstdf[3*ext+4]^((q-1)/2))^((v*s*w.spnstdf[3*ext+3])^(-1)))*(v*s);
        w.spnstdf[3*ext+1] := v;

        newbasechange := PermMat3^(-1)*basechange;
        w.bas := PermMat3^(-1) * w.bas;
        w.basi := w.basi * PermMat3;

        # Now add the new transvections:
        for i in [Size(transd)/2+1..Size(transd)] do
            # w.transh[w.ext*(w.n-1)+w.ext*(i-1)+1] := transr[i];
            Add(w.transh1, transd[i]^(-1));
        od;
        newtransv := transd{[1..Size(transd)/2]};
        Append(newtransv,w.transh2);
        w.transh2 := newtransv;
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
        PermMat3 := RECOG.ComputeCorrectingPermutationMatSp(d,F,n,aimdim);
        v := w.spnstdf[3*ext+1];
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

            v := ((w.spnstdf[3*ext+4]^((q-1)/2))^((v*s*w.spnstdf[3*ext+3])^(-1)))*(v*s);
            w.spnstdf[3*ext+1] := v;
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
                v := ((w.spnstdf[3*ext+4]^((q-1)/2))^((v*s*w.spnstdf[3*ext+3])^(-1)))*(v*s);
            else
                v := (v*s);
            fi;
            w.spnstdf[3*ext+1] := v;
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

    flag := false;
    s := w.One;
    PermMat3 := RECOG.ComputeCorrectingPermutationMatSp(d,F,n,aimdim);
    v := w.spnstdf[3*ext+1];
    for i in [n-2,n-3..(n/2)] do
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
    v := (v*s);
    w.spnstdf[3*ext+1] := v;

    newbasechange := PermMat3^(-1)*basechange;
    w.bas := PermMat3^(-1) * w.bas;
    w.basi := w.basi * PermMat3;

    # Now add the new transvections:
    begintransv := Size(transd)/2+1;
    difftransv := Size(transd) -  Size(transd)/2;
    for i in [1..difftransv/w.ext] do
        for k in [1..w.ext] do
            Add(w.transh1, transd[Size(transd)-i*w.ext+k]^(-1));
        od;
    od;

    # TODO: Here is still something mixed to shift the transvections for the next run. If this is fixed, remove the command w.transh2 := [] at the beginning of this function

    #newtransv := [];
    #for i in [1..difftransv/w.ext] do
        # w.transh[w.ext*(w.n-1)+w.ext*(i-1)+1] := transr[i];
    #    for k in [1..w.ext] do
    #        Add(newtransv, transd[Size(transr)-i*w.ext+k]);
    #    od;
    #od;
    #Append(newtransv,w.transh2);
    #w.transh2 := newtransv;
    w.n := aimdim;

    Info(InfoRecog,2,"Step 7 done");
    return w;
end;
