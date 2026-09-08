#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This files's authors include Daniel Rademacher, Max Neunhöffer, Ákos Seress.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
#############################################################################



#############################################################################
#############################################################################
######## General utils ######################################################
#############################################################################
#############################################################################



InstallOtherMethod( \-, "for two memory elements",
  [ IsMatrix and IsObjWithMemory, IsMatrix and IsObjWithMemory ],
  function(m,n)
    return m!.el - n!.el;
  end );



#############################################################################
#############################################################################
######## CheckStingrayGroup #################################################
#############################################################################
#############################################################################


RECOG.CheckNewStingrayGroup := function(g1,base1,g2,base2,q)
local baseSum, module;

    baseSum := Concatenation(base1,base2);
    baseSum := TriangulizedMat(baseSum);
    if IsZero(Last(baseSum)) then
        return false;
    fi;

    g1 := TransposedMat(StripMemory(g1));
    g2 := TransposedMat(StripMemory(g2));
    module := GModuleByMats( [g1,g2], GF(q) );
    module := MTX.InducedActionSubmoduleNB( module, baseSum );
    return MTX.IsIrreducible(module);
end;



#############################################################################
#############################################################################
######## ConstructSmallSub ##################################################
#############################################################################
#############################################################################



RECOG.ConstructSmallSub := function(r1, r2, product, newbasis, detectFun)
    local gens, pseudoorderlist, Hsub, productEle, ele, ele2, H, cord1, cord2;

    gens := [];
    pseudoorderlist := [];
    Hsub := [];
    repeat
        productEle := PseudoRandom(product);
        Add(Hsub, productEle);
        ele := (productEle)^(newbasis^(-1));
        ele2 := ele{r2}{r2};
        ele := ele{r1}{r1};
        Add(pseudoorderlist, RECOG.EstimateOrder(ele2)[1]);
        Add(gens,ele);
    until Size(gens) = 2;
    H := GroupByGenerators(gens);
    if detectFun(H) = true then
        cord1 := Order(gens[1]);
        cord2 := Order(gens[2]);
        if (Gcd(cord1,pseudoorderlist[1]) <> pseudoorderlist[1]) and (Gcd(cord2,pseudoorderlist[2]) <> pseudoorderlist[2]) then
            gens[1] := gens[1]^pseudoorderlist[1];
            gens[2] := gens[2]^pseudoorderlist[2];
            H := GroupByGenerators(gens);
            if detectFun(H) = true then
                Hsub[1] := Hsub[1]^pseudoorderlist[1];
                Hsub[2] := Hsub[2]^pseudoorderlist[2];
                return [Hsub,H,newbasis];
            fi;
        fi;
    fi;
    return fail;
end;

#############################################################################
#############################################################################
######## constructppdTwoStingray ############################################
#############################################################################
#############################################################################



RECOG.constructppdTwoStingray := function(g,dim,q,type,form)
  local out, list, out2, currentdim, aimdim, godown;

  if type = "SL" then
    aimdim:=-1;
  elif type = "O" then
    aimdim:=8;
  elif type = "Sp" then
    aimdim:=8;
  elif type = "SU" then
    if IsEvenInt(q) then
      aimdim := 10;
    else
      aimdim := 6;
    fi;
  else
    Error("unsupported type ", type);
  fi;

  Info(InfoRecog,2,"Current Dimension: ", dim, " for type ", type);
  Info(InfoRecog,2,"\n");

  list:=[g,dim,q,fail,form];
  currentdim := dim;
  repeat
     out:=RECOG.godownStingray(list,type);
     if out=fail or IsOne(out[1]^2) then
        Info(InfoRecog,2,"Restart. \n");
        Info(InfoRecog,2,"Current Dimension: ");
        Info(InfoRecog,2,dim);
        Info(InfoRecog,2,"\n");
        list:=[g,dim,q,fail,form];
        out:=fail;
     else
        if type = "SL" and out[2] = 2 then
          return out[1];
        fi;
        Assert(0, out[1] >= 2);
        repeat
             out2:=RECOG.godownStingray(list,type);
             if out2=fail or out2[1]*out2[1]=One(out2[1]) then
                 if InfoLevel(InfoRecog) >= 3 then Print("B\c"); fi;
                 list:=[g,dim,q,fail,form];
                 out2:=fail;
             fi;
        until out2<>fail and out2[2] >= 2;
        if type = "SL" and out2[2] = 2 then
            return out2[1];
        fi;
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



#############################################################################
#############################################################################
######## godownStingray #####################################################
#############################################################################
#############################################################################



# finds first element of a list that is relative prime to all others
# input: list=[Sp(d,q), d, q, Sp(n,q)] acting as a subgroup of some big Sp(n,q)
# output: list=[rr, dd] for a ppd(2*dd;q)-element rr
RECOG.godownStingray := function(list,type)
local d, firstSL, firstSU, q, p, g, i, r, pol, factors, degrees, newdim, power, rr, ss, max,
newgroup, colldegrees, exp, count, check, ocount, beta, NiList, Maxi, qFactors, 
irrfact, invbase, form, CheckOtherFactors, CheckFactors, fld, restricted, b, j;

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

    firstSU := function(list)
    local i, j, goodElement;
        for i in [1..Length(list)] do
            if list[i]>1 and (list[i] mod 2 = 1) then
                if Gcd(list[i],Product(list)/list[i]) < list[i] then
                    return i;
                else
                    goodElement := true;
                    for j in [1..Length(list)] do
                        if not(j = i) and Gcd(list[i],list[j]) = list[i] then
                            goodElement := false;
                            break;
                        fi;
                    od;
                    if goodElement then
                        return i;
                    fi;
                fi;
            fi;
        od;
        return fail;
    end;

    firstSL := function(list)
    local i, j, goodElement;
        for i in [1..Length(list)] do
            if list[i]>1 then
                if Gcd(list[i],Product(list)/list[i]) < list[i] then
                    return i;
                else
                    goodElement := true;
                    for j in [1..Length(list)] do
                        if not(j = i) and Gcd(list[i],list[j]) = list[i] then
                            goodElement := false;
                            break;
                        fi;
                    od;
                    if goodElement then
                        return i;
                    fi;
                fi;
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

    if type = "SL" then
        max := Maximum([Log2Int(d),3]);
    elif type = "Sp" then
        max := Maximum([2*Log2Int(d),3]);
    elif type = "SU" then
        max := Maximum([2*Log2Int(d),3]);
    elif type = "O" then
        max := Maximum([2*Log2Int(d),3]);
    else
        Error("type not supported");
    fi;

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
            if type = "SL" then
                newdim:= firstSL(degrees);
            elif type = "SU" then
                newdim:= firstSU(degrees); 
            elif type = "O" or type = "Sp" then
                newdim := CheckFactors(degrees, factors);
            else
                Error("type not supported");
            fi;
        until (count>100) or (newdim <> fail and (degrees[newdim] < max));
        # Be careful if Log2Int(d) = 2! In this case we search for stingray elements with k < 2. Hence use newdim < Maximum([Log2Int(d),3])

        if count>100 then
            return fail;
        fi;
        
        # Split result from first:
        irrfact := factors[newdim];
        newdim := degrees[newdim];

        if newdim = 2 and type = "SL" then
            check := true;
        else
            # Check whether the stingray candidate is a ppd-stingray element
            check := RECOG.IsPpdStingrayElement(p,Length(qFactors),newdim,irrfact);
        fi;

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

            if newdim = 2 and type = "SL" then
                if Size(invbase) = 2 then
                    return [rr,newdim,invbase];
                fi;
            else

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
        fi;
        
        ocount := ocount + 1;
    od;

    return fail;

end;



#############################################################################
#############################################################################
######## Check PPD-Property and tests #######################################
#############################################################################
#############################################################################



##  This function takes as input:
##
##  <F>  field
##  <f>  a characteristic polynomial
##  <d>  degree of <m>
##  <p>  a prime power
##  <a>  an integer
##  <irrfact> an irreducible factor of <f> and of degree a

RECOG.IsPpdStingrayElement := function( p, f, k, irrfact )
    local c, e,  R,  pm,  g, islarge, F;

    F := GF(p^f);
    c := irrfact;
    R := PolynomialRing(F);

    e  := k;
    ## find the noppds and ppds parts
    pm := PrimitivePrimeDivisors( f*e, p );
    ## pm contains two fields, noppds and ppds.
    ## ppds is the product of all ppds of p^(ae)-1
    ## and noppds is p^(ae)-1/ppds.

    ## get rid of the non-ppd part
    ## g will be x^noppds in F[x]/<c>
    g := PowerMod( Indeterminate(F), pm.noppds, c );

    ## now we know that <m> is a ppd-element

    ## if g is one there is no ppd involved
    if IsOne(g) then
        return false;
    else
        return true;
    fi;

    #if IsOne(g)  then
    #    ## (e+1) is the only ppd dividing |<m>| and only once
    #    islarge := false;
    #    return [ e, islarge ];
    #else
    #    ## Either another ppd also divides |<m>| and this one is large or
    #    ## (e+1)^2 divides |<m>| and hence still large
    #    islarge := true;
    #    return [ e, islarge  ];
    #fi;


end;



#############################################################################
#############################################################################
######## Linear action representation #######################################
#############################################################################
#############################################################################



RECOG.LinearAction := function(bas,field,el)
  local mat,vecs;
  if IsGroup(el) then
      return Group(List(GeneratorsOfGroup(el),
                        x->RECOG.LinearAction(bas,field,x)));
  fi;
  if IsBasis(bas) then
      vecs := BasisVectors(bas);
  else
      vecs := bas;
      bas := Basis(VectorSpace(field,bas),bas);
  fi;
  mat := List(vecs,v->Coefficients(bas,v*el));
  ConvertToMatrixRep(mat,field);
  return mat;
end;







RECOG.LinearActionRepresentation := function(G)
local OldGens, newGens, i, base, fld, d, EleBase, fixbase, B, action, ele, V;
    
    OldGens := ShallowCopy(GeneratorsOfGroup(G));
    for i in [1..Length(OldGens)] do
        if IsObjWithMemory(OldGens[i]) then
            OldGens[i] := StripMemory(OldGens[i]);
        fi;
    od;
    
    fld := FieldOfMatrixList(OldGens);
    d := Size(OldGens[1]);
    base := [];
    for i in [1..Length(OldGens)] do
        ele := OldGens[i];
        fixbase := RECOG.FixspaceMat(TransposedMat(ele));
        if fixbase = [] then
            return fail;
        fi;
        EleBase := NullspaceMat(TransposedMat(fixbase));
        Append(base,EleBase);
    od;
    
    V := VectorSpace(fld,base);
    B := Basis(V);
    base := BasisVectors(B);
    newGens := [];
    for i in [1..Length(OldGens)] do
        ele := OldGens[i];
        action := List(base,v->Coefficients(B,v*ele));
        Add(newGens,action);
    od;
    
    return GroupByGenerators(newGens);
end;


#############################################################################
#############################################################################
######## Self-conjugate polynomial check ####################################
#############################################################################
#############################################################################



RECOG.CheckPolynomialForSelfConjugate := function (f)
local ind, coeff, a0, i, deg, pol;
    # TODO: this function could be optimized: no need to construct the new
    # polynomial, just directly work with coeff
    ind := IndeterminateOfLaurentPolynomial(f);
    coeff := CoefficientsOfUnivariatePolynomial(f);
    deg := Length(coeff);
    a0 := coeff[1];

    pol := ind * 0;
    for i in [1..deg] do
        pol := pol + ind^(deg-i)*coeff[i];
    od;
    
    pol := a0 * pol;

    return pol = f;
end;




#############################################################################
#############################################################################
######## Extract and rescale block matrices #################################
#############################################################################
#############################################################################



RECOG.ComputeBlockBaseChangeMatrix := function(list,d,q)
local fixbase, elebase, basis, matrix, fix, moved, currentmove, currentfix, k, newbase, OldGens, i;

    OldGens := ShallowCopy(list);
    for i in [1..Length(OldGens)] do
        if IsObjWithMemory(OldGens[i]) then
            OldGens[i] := StripMemory(OldGens[i]);
        fi;
    od;
    list := OldGens;

    fix := [];
    moved := [];

    for matrix in list do;
        fixbase := RECOG.FixspaceMat(TransposedMat(matrix));
        elebase := NullspaceMat(TransposedMat(fixbase));
        Add(moved, elebase);

        fixbase := RECOG.FixspaceMat(matrix);
        Add(fix,fixbase);
    od;

    if Size(moved) = 1 then
        newbase := MutableCopyMat(moved[1]);
        Append(newbase,fix[1]);
        return newbase;
    else
        currentmove := MutableCopyMat(moved[1]);
        currentfix := MutableCopyMat(fix[1]);
        k := 1;
        while k < Size(moved) do
            currentmove := SumIntersectionMat(currentmove,moved[k+1])[1];
            currentfix := SumIntersectionMat(currentfix,fix[k+1])[2];
            k := k + 1;
        od;
        Append(currentmove,currentfix);
        return currentmove;
    fi;

end;



RECOG.ExtractSmallerGroup := function(list,basechange,size)
local gens, ele, block, OldGens, i;

    OldGens := ShallowCopy(list);
    for i in [1..Length(OldGens)] do
        if IsObjWithMemory(OldGens[i]) then
            OldGens[i] := StripMemory(OldGens[i]);
        fi;
    od;
    list := OldGens;

    gens := [];
    for ele in list do
        block := (ele^(basechange^(-1)));
        block := block{[1..size]}{[1..size]};
        Add(gens,block);
    od;

    return [GroupByGenerators(gens),gens];
end;



RECOG.LiftGroup := function(list,size,q,d)
local gens, ele, block, OldGens, i;

    OldGens := ShallowCopy(list);
    for i in [1..Length(OldGens)] do
        if IsObjWithMemory(OldGens[i]) then
            OldGens[i] := StripMemory(OldGens[i]);
        fi;
    od;
    list := OldGens;

    gens := [];
    for ele in list do
        block := IdentityMat(d,GF(q));
        block{[1..size]}{[1..size]} := ele;
        Add(gens,block);
    od;

    return [GroupByGenerators(gens),gens];
end;



#############################################################################
#############################################################################
######## Membership test in groups preserving a form ########################
#############################################################################
#############################################################################


# given a matrix `mat`, test if it is contained in G, which must be Omega(e,n,fld)
#
# TODO: add unit tests
#
# e:=+1; d:=8; q:=8;
# G:=Omega(e,d,q);
# H:=SO(e,d,q,InvariantQuadraticForm(G).matrix);
# ForAll(GeneratorsOfGroup(G), g -> g in H);
# ForAll(GeneratorsOfGroup(G), g -> IsInOmega(G, g));
# ForAll(GeneratorsOfGroup(H), g -> IsInOmega(G, g));
#
RECOG.IsInOmega:=function(G,mat)
  local d, Q, form, fld;
  d := DimensionOfMatrixGroup(G);
  fld := FieldOfMatrixGroup(G);
  Assert(0, NrRows(mat) = d);

  # first verify the quadratic form is preserved
  Q := InvariantQuadraticForm(G).matrix;
  if not RespectsQuadraticForm(Q, mat) then
    return false;
  fi;

  if Characteristic(fld) <> 2 then
    form := InvariantBilinearForm(G).matrix;
    return IsOne(SpinorNorm(form, fld, mat));
  elif IsOddInt(d) then
    # Omega(0,2n+1,2^k) = SO(0,2n+1,2^k) = GO(0,2n+1,2^k)
    return true;
  else
    # the following is based on Lemma 3.5(2) in Holt, Roney-Dougal:
    # "Constructing maximal subgroups of orthogonal groups"
    return IsEvenInt(RankMat(mat + One(G)));
  fi;
end;



# Assuming that the group G acts absolutely irreducibly, try to find a
#   * symplectic form (if <type> = S) or a
#   * symmetric bilinear form (if <type> = O)
# which is G-invariant or prove that no such form exists.
#
# We use this function instead of PreservedBilinearForms form the Forms package
# since PreservedBilinearForms seems to be buggy and unreliable (see also
# comment above UnitaryForm).
#
# In general, this function should only be used if one can be sure that <G>
# preserves a bilinear form (but one does not know which one).
RECOG.BilinearForm := function(G, type)
    local F, M, inverseTransposeM, counter, formMatrix, condition;

    if not type in ["S", "O"] then
        ErrorNoReturn("<type> must be one of 'S', 'O'");
    fi;
    # Set the condition the Gram matrix needs to satisfy for each of the
    # possible types.
    if type = "S" then
        condition := x -> (x = - TransposedMat(x));
    elif type = "O" then
        condition := x -> (x = TransposedMat(x));
    fi;

    F := DefaultFieldOfMatrixGroup(G);

    # Return stored bilinear form if it exists and is symplectic / symmetric
    if HasInvariantBilinearForm(G) then
        formMatrix := InvariantBilinearForm(G).matrix;
        if condition(formMatrix) then
            return ImmutableMatrix(F, formMatrix);
        fi;
    fi;
    
    M := GModuleByMats(GeneratorsOfGroup(G), F);

    if not MTX.IsIrreducible(M) then
        ErrorNoReturn("BilinearForm failed - group is not irreducible");
    fi;

    # An element A of G acts as A ^ (-T) in MTX.DualModule(M)
    inverseTransposeM := MTX.DualModule(M);

    counter := 0;
    # As the MeatAxe is randomised, we might have to make some more trials to
    # find a preserved symplectic / symmetric bilinear form if there is one;
    # breaking after 1000 trials is just a "safety net" in case a group <G>
    # that does not preserve a symplectic / symmetric bilinear form is input.
    while counter < 1000 do
        counter := counter + 1;

        # If f: M -> inverseTransposeM is an isomorphism, it must respect
        # multiplication by group elements, i.e. for A in G
        #       f(x * A) = f(x) * A ^ (-T)
        # Let f be given by the matrix F, i.e. f: x -> x * F. Then we have
        #       (x * A) * F = x * F * A ^ (-T)
        # Putting these results together for all vectors x gives
        #       A * F = F * A ^ (-T)
        # <==>  A * F * A ^ T = F,
        # which is what we need.
        formMatrix := MTX.IsomorphismModules(M, inverseTransposeM);

        if formMatrix <> fail then
            # check if formMatrix is antisymmetric
            if condition(formMatrix) then
                return ImmutableMatrix(F, formMatrix);
            fi;
            if not MTX.IsAbsolutelyIrreducible(M) then
                ErrorNoReturn("BilinearForm failed - group is not absolutely irreducible");
            fi;
        fi;
    od;

    return fail;
end;

RECOG.SymplecticForm := function(G)
    return RECOG.BilinearForm(G, "S");
end;

RECOG.SymmetricBilinearForm := function(G)
    return RECOG.BilinearForm(G, "O");
end;



#############################################################################
################## Old function from RECOG package ##########################
#############################################################################
#############################################################################


RECOG.DerivedSubgroupMonteCarlo := function(g, NumberGenerators)
  local gens,gens2,i,x,y;
  gens := [];
  for i in [1..Maximum([NumberGenerators, Size(GeneratorsOfGroup(g)) * 2 + 10])] do
      x := PseudoRandom(g);
      y := PseudoRandom(g);
      Add(gens,Comm(x,y));
  od;
  gens2 := FastNormalClosure(GeneratorsOfGroup(g),gens,10);
  return GroupWithGenerators(gens2);
end;
