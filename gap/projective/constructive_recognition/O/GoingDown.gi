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
######## GoingDown method for orthogonal groups #############################
#############################################################################
#############################################################################



RECOG.SO_godownToDimension6 := function(h,q)
local counter, ele, x, x2, ord, invo, found, cent, product, eigenspace, Minuseigenspace, newbasis, dimeigen, dimMinuseigen, r1, r2, result;

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
        r1 := [1..dimeigen];
        r2 := [7,8];
    else
        r1 := [dimeigen+1..8];
        r2 := [1,2];
    fi;
    for counter in [1..100] do
        result := RECOG.ConstructSmallSub(r1, r2, product, newbasis, g -> RecogniseClassical(g).isSOContained);
        if result <> fail then
            break;
        fi;
    od;

    return result;

end;



RECOG.SOn_constructso2:=function(g,d,q,form)
local r,h,basechange,basechange2,slp,liftbasechange2,liftr;

    r := RECOG.constructppdTwoStingray(g,d,q,"O",form);
    Info(InfoRecog,2,"Finished main GoingDown, i.e. we found a stringray element which operates irreducible on a 8 dimensional subspace. \n");
    # Remark D.R.: at this point we know that h is isomorphic to Omega(8,q)
    Info(InfoRecog,2,"Succesful. ");
    Info(InfoRecog,2,"Current Dimension: 8\n");
    Info(InfoRecog,2,"Next goal: Generate Omega(4,q). \n");
    if IsEvenInt(q) then
        basechange := RECOG.ComputeBlockBaseChangeMatrix(GeneratorsOfGroup(r),d,q);
        liftr := List(GeneratorsOfGroup(r),x->x^(basechange^(-1)));
        return [GroupByGenerators(liftr),basechange];
    else
        # For now, compute a base change into the stingray matrices
        basechange := RECOG.ComputeBlockBaseChangeMatrix(GeneratorsOfGroup(r),d,q);
        #slp := SLPOfElms(GeneratorsOfGroup(r));

        r := RECOG.SO_godownToDimension6(RECOG.ExtractSmallerGroup(GeneratorsOfGroup(r),basechange,8)[1],q);
        basechange2 := RECOG.ComputeBlockBaseChangeMatrix(r[1],8,q);
        liftbasechange2 := RECOG.LiftGroup([basechange2],8,q,d)[2,1];
        liftr := RECOG.LiftGroup(r[1],8,q,d)[2];

        liftr := List(liftr,x->x^(liftbasechange2^(-1)));
        #slp := CompositionOfStraightLinePrograms(SLPOfElms(r[1]),slp);
        # Remark D.R.: at this point we know that h is isomorphic to Sp(6,q)

        return [GroupByGenerators(liftr),liftbasechange2*basechange];
    #   return ["sorry only SL(4,q)",h];
    fi;
end;
