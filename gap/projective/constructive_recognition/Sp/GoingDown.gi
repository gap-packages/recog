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
######## GoingDown method for symplectic groups #############################
#############################################################################
#############################################################################



RECOG.Sp_godownToDimension6 := function(h,q)
local counter, ele, x, x2, ord, invo, found, cent, product, eigenspace, Minuseigenspace, newbasis, dimeigen, dimMinuseigen, r1, r2, result;

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
                if dimeigen = 6 or dimMinuseigen = 6 then
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

    # Second we compute the two factors by computing the centralizer of the involution i

    cent := RECOG.CentraliserOfInvolution(h,invo,[],true,100,RECOG.CompletionCheck,PseudoRandom);
    product := GroupByGenerators(cent[1]);

    # Third we continue as in "Constructive recognition of classical groups in odd characteristic" part 11 to find generator

    if dimeigen = 6 then
        r1 := [1..6];
        r2 := [7..8];
    else
        r1 := [3..8];
        r2 := [1..2];
    fi;
    for counter in [1..100] do
        result := RECOG.ConstructSmallSub(r1, r2, product, newbasis, g -> RecogniseClassical(g).isSpContained);
        if result <> fail then
            break;
        fi;
    od;

    return result;

end;


# This function is sometimes slow ---> some problem after computing tau. Is tau correct???
# Construct a naturally embedded Sp4 of Sp6
RECOG.Sp_godownToDimension4 := function(h,q)

    if not(IsObjWithMemory(GeneratorsOfGroup(h)[1])) then
        h := GroupWithMemory(h);
    fi;

    if q <= 5 then
        return RECOG.ConstructSp4OddSmall(h,q);
    else
        return RECOG.ConstructSp4OddLarge(h,q);
    fi;

end;



RECOG.IsSp4SmallTauElement := function(tau,q,list)
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



# called by Sp_godownToDimension4 to construct a naturally embedded Sp4 of Sp6
# ConstructJOddSmall in Clarkson's thesis
RECOG.ConstructSp4OddSmall := function(h,q)
local tau, t, g1, g2, g3, g, counter, testgroup, smalltestgroup, preparelist, k, newentry, ppd, new, p, reco;

    counter := 1;

    preparelist := [];
    p := Factors(q)[1];
    # TODO: Adjust to ppd# elements. See Dissertation Kenneth Clarkson (Eamonns student)
    for k in [1..10] do
        new := [k];
        ppd := PrimitivePrimeDivisors( 4*k, p );
        Add(new,PrimeDivisors(ppd.ppds));
        Add(preparelist,new);
    od;

    Info(InfoRecog,2,"Precomputation finished");

    while counter < 100 do
        tau := PseudoRandom(h);
        if RECOG.IsSp4SmallTauElement(tau,q,preparelist) and (Order(tau^(q^2+1)) <> 1) then
            t := tau^(q^2+1);
            #a := tau^(2*(q^2-q+1));
            Info(InfoRecog,2,"Found tau");
            while counter < 100 do
                g1 := PseudoRandom(h);
                g2 := PseudoRandom(h);
                g3 := PseudoRandom(h);
                testgroup := GroupByGenerators([t,t^g1,t^g2,t^g3]);
                smalltestgroup := RECOG.LinearActionRepresentation(testgroup);
                reco := RecogniseClassical(smalltestgroup);
                if (reco.d = 4) and reco.isSpContained then
                    Info(InfoRecog,2,"Found Sp(4,q)");
                    return [testgroup,smalltestgroup];
                fi;
                counter := counter + 1;
            od;
        fi;
        counter := counter + 1;
    od;

    return fail;

end;



RECOG.IsSp4LargeTauElement := function(tau,q,list,extra)
local entry, foundFirst, foundSecond, ppdk, ppd4k, ord, prime;

    ord := Order(tau);
    entry := extra;
    if Size(DuplicateFreeList(Factors(ord))) <> 1 then
        ppd4k := entry[2];
        for prime in ppd4k do
            if (ord mod prime = 0) then
                return true;
            fi;
        od;
    fi;
    for entry in list do
        foundFirst := false;
        foundSecond := false;

        ppdk := entry[2];
        for prime in ppdk do
            if (ord mod prime = 0) then
                foundFirst := true;
                break;
            fi;
        od;

        if foundFirst then
            ppd4k := entry[3];
            for prime in ppd4k do
                if (ord mod prime = 0) then
                    return true;
                fi;
            od;
        fi;

    od;

    return false;
end;



# Next function correct???
RECOG.ConstructSp4OddLarge := function(h,q)
local tau, a, g, counter, testgroup, smalltestgroup, preparelist, k, newentry, ppd, new, p, reco, extra;

    counter := 1;

    preparelist := [];
    p := Factors(q)[1];
    # TODO: Adjust to ppd# elements. See Dissertation Kenneth Clarkson (Eamonns student)
    if (q mod 2 = 0) then
        # TODO
    else
        extra := [1,PrimeDivisors(PrimitivePrimeDivisors( 1, p ).ppds)];
        for k in [2..10] do
            new := [k];
            ppd := PrimitivePrimeDivisors( k, p );
            Add(new,PrimeDivisors(ppd.ppds));
            ppd := PrimitivePrimeDivisors( 4*k, p );
            Add(new,PrimeDivisors(ppd.ppds));
            Add(preparelist,new);
        od;
    fi;

    Info(InfoRecog,2,"Precomputation finished");

    while counter < 100 do
        tau := PseudoRandom(h);
        if RECOG.IsSp4LargeTauElement(tau,q,preparelist,extra) and (Order(tau^(q^2+1)) <> 1) then
            a := tau^(q^2+1);
            #a := tau^(2*(q^2-q+1));
            Info(InfoRecog,2,"Found tau");
            while counter < 100 do
                g := PseudoRandom(h);
                testgroup := GroupByGenerators([a,a^g]);
                smalltestgroup := RECOG.LinearActionRepresentation(testgroup);
                if smalltestgroup <> fail then
                    reco := RecogniseClassical(smalltestgroup);
                    if (reco.d = 4) and reco.isSpContained = true then
                        Info(InfoRecog,2,"Found Sp(4,q)");
                        return [testgroup,smalltestgroup];
                    fi;
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



RECOG.Spn_constructsp4:=function(g,d,q,form)
local r,h,basechange,basechange2,basechange3,liftbasechange2,liftbasechange3,liftr,i,rr,slp;

    if IsEvenInt(q) then
        Error("not supported");
    fi;

    r := RECOG.constructppdTwoStingraySpO(g,d,q,form);
    Info(InfoRecog,2,"Finished main GoingDown, i.e. we found a natural embedded Sp(8,q). \n");

    # For now, compute a base change into the stingray matrices
    basechange := RECOG.ComputeBlockBaseChangeMatrix(GeneratorsOfGroup(r),d,q);
    slp := SLPOfElms(GeneratorsOfGroup(r));

    r := RECOG.Sp_godownToDimension6(RECOG.ExtractSmallerGroup(GeneratorsOfGroup(r),basechange,8)[1],q);
    basechange2 := RECOG.ComputeBlockBaseChangeMatrix(r[1],8,q);
    slp := CompositionOfStraightLinePrograms(SLPOfElms(r[1]),slp);
    # Remark D.R.: at this point we know that h is isomorphic to Sp(6,q)
    Info(InfoRecog,2,"Succesful. ");
    Info(InfoRecog,2,"Current Dimension: 6\n");
    Info(InfoRecog,2,"Next goal: Generate Sp(4,q). \n");

    i := 1;
    repeat
        rr := RECOG.Sp_godownToDimension4(RECOG.ExtractSmallerGroup(r[1],basechange2,6)[1],q);
        i := i + 1;
    until i >= 10 or rr <> fail;

    r := rr;
    if r = fail then
        return fail;
    fi;
    slp := CompositionOfStraightLinePrograms(SLPOfElms(GeneratorsOfGroup(r[1])),slp);
    basechange3 := RECOG.ComputeBlockBaseChangeMatrix(GeneratorsOfGroup(r[1]),6,q);

    liftbasechange2 := RECOG.LiftGroup([basechange2],8,q,d)[2,1];
    liftbasechange3 := RECOG.LiftGroup([basechange3],6,q,d)[2,1];

    liftr := RECOG.LiftGroup(GeneratorsOfGroup(r[1]),6,q,d)[2];
    for i in [1..Size(liftr)] do
        liftr[i] := liftr[i]^(liftbasechange3^(-1));
    od;

    return [GroupByGenerators(liftr),liftbasechange3*liftbasechange2*basechange,[basechange,liftbasechange2,liftbasechange3],slp];
end;




RECOG.godownStingraySpO := function(list)
local d, q, p, g, i, r, pol, factors, degrees, newdim, power, rr, ss, max, newgroup, colldegrees, exp, count, check, ocount, beta, NiList, Maxi, qFactors, irrfact, invbase, CheckOtherFactors, CheckFactors, form, fld, restricted, b, j;

    CheckOtherFactors := function(i, deg, fact)
    local j;
    for j in [1..Length(deg)] do
        if not(j = i) then
            if RECOG.CheckPolynomialForSelfConjugate(fact[j]) then
                if (deg[j] mod deg[i] = 0) then
                    return false;
                fi;
            else
                if (deg[j] mod Int(deg[i]/2) = 0) then
                    return false;
                fi;
            fi;
        fi;
    od;
    return true;
    end;

    CheckFactors := function(deg, fact)
    local i;
        for i in [1..Length(deg)] do
            if ((deg[i] mod 2) = 0) and RECOG.CheckPolynomialForSelfConjugate(fact[i]) and CheckOtherFactors(i,deg,fact) then
            return i;
            fi;
        od;
        return fail;
    end;

    g:=list[1];
    d:=list[2];
    q:=list[3];
    qFactors:=Factors(q);
    p := qFactors[1];
    form := list[5];
    fld := GF(q);

    max := Maximum([2*Log2Int(d),3]);

    # Overall count. Replace by formula and unequality
    ocount := 0;
    while ocount < 100 do

        Info(InfoRecog,2,"Dimension: ",d);
        #find an element with irreducible action of relative prime dimension to
        #all other invariant subspaces
        #count is just safety, if things go very bad
        count:=0;

        repeat
            count:=count+1;
            r:=PseudoRandom(g);
            pol:=CharacteristicPolynomial(r);
            factors:=Factors(pol);
            degrees:=List(factors,Degree);
            newdim := CheckFactors(degrees, factors);
        until (count>100) or (newdim <> fail and (degrees[newdim] < max));
        # Be careful if Log2Int(d) = 2! In this case we search for stingray elements with k < 2. Hence use newdim < Maximum([Log2Int(d),3])

        if count>100 then
            return fail;
        fi;
        
        # Split result from first:
        irrfact := factors[newdim];
        newdim := degrees[newdim];

            # Check whether the stingray candidate is a ppd-stingray element
            check := RECOG.IsPpdStingrayElement(p,Length(qFactors),newdim,irrfact);

        if check then
        
            # raise r to a power so that acting trivially outside one invariant irreducible subspace
            NiList := Collected(degrees);
            NiList := Filtered(NiList,x->not(x[1] = newdim));
            colldegrees := List(NiList,x->x[1]);
            NiList := List(NiList,x->x[2]);
            Maxi := Maximum(NiList);
            beta := LogInt(Maxi,p);
            if not(p^beta = Maxi) then
                beta := beta + 1;
            fi;
            
            # power further to cancel q-part of element order
            power := Lcm(List(colldegrees, x->q^x-1))*p^beta;
            rr:=r^power;

            invbase := NullspaceMat(TransposedMat(RECOG.FixspaceMat(StripMemory(rr))));


                #if (type = "SL") or (IsEvenInt(q) and type = "SU") then
                #    return [rr,newdim,invbase];
                #fi;
                
                #b := Basis(VectorSpace(fld,invbase),invbase);
                #restricted := IdentityMat(newdim,fld);
                #for i in [1..newdim] do
                #    for j in [1..newdim] do
                #        restricted[i,j] := b[i]*form*b[j];
                #    od;
                #od;
                
                #if IsEmpty(NullspaceMat(restricted)) then
                    return [rr,newdim,invbase];
                #else
                #    Error("here");
                #fi;
        fi;
        
        ocount := ocount + 1;
    od;

    return fail;

end;


RECOG.constructppdTwoStingraySpO := function(g,dim,q,form)
  local out, list, out2, currentdim, aimdim;

  aimdim := 8;

  Info(InfoRecog,2,"Current Dimension: ", dim, " for type Sp");
  Info(InfoRecog,2,"\n");

  list:=[g,dim,q,fail,form];
  currentdim := dim;
  repeat
     out:=RECOG.godownStingraySpO(list);
     if out=fail or IsOne(out[1]^2) then
        Info(InfoRecog,2,"Restart. \n");
        Info(InfoRecog,2,"Current Dimension: ");
        Info(InfoRecog,2,dim);
        Info(InfoRecog,2,"\n");
        list:=[g,dim,q,fail,form];
        out:=fail;
     else
        Assert(0, out[1] >= 2);
        repeat
             out2:=RECOG.godownStingraySpO(list);
             if out2=fail or out2[1]*out2[1]=One(out2[1]) then
                 if InfoLevel(InfoRecog) >= 3 then Print("B\c"); fi;
                 list:=[g,dim,q,fail,form];
                 out2:=fail;
             fi;
        until out2<>fail and out2[2] >= 2;
        if RECOG.CheckNewStingrayGroup(out[1],out[3],out2[1],out2[3],q) then
             list:=[Group(out[1],out2[1]),out[2]+out2[2],q,fail,form];
             currentdim := list[2];

             Info(InfoRecog,2,"Debug Info:\n");
             Info(InfoRecog,2,"Dimension FirstElement: ");
             Info(InfoRecog,2,out[2]);
             Info(InfoRecog,2,"\n");
             Info(InfoRecog,2,"Dimension SecondElement: ");
             Info(InfoRecog,2,out2[2]);
             Info(InfoRecog,2,"\n");
             Info(InfoRecog,2,"End Debug Info. \n");
           
             Info(InfoRecog,2,"New Dimension: ");
             Info(InfoRecog,2,out[2]+out2[2]);
             Info(InfoRecog,2,"\n");
        else
             if InfoLevel(InfoRecog) >= 3 then Print("B\c"); fi;
             Info(InfoRecog,2,"Restart. \n");
             Info(InfoRecog,2,"Current Dimension: ");
             Info(InfoRecog,2,dim);
             Info(InfoRecog,2,"\n");
             list:=[g,dim,q,fail,form];
             out:=fail;
        fi;
     fi;
  until currentdim=aimdim;

  return list[1];

end;