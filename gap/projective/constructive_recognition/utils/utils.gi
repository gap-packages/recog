#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This files's authors include Max Neunhöffer, Ákos Seress, Daniel Rademacher.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
#############################################################################

# For the constructive recognition of classical groups in their natural
# representation: level 1 reports the phases, 2 each step, 3 each rejected
# random element.
DeclareInfoClass( "InfoRecog_ClassicalNatural" );

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

# Whether <base1> and <base2> span independent subspaces on whose sum
# <g1> and <g2> act irreducibly.
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

# Two random elements of <product> whose blocks r1, relative to <newbasis>,
# satisfy <detectFun>, powered so that they act trivially on the blocks r2.
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

# Whether a root of the irreducible factor <irrfact>, of degree <k>, of a
# characteristic polynomial over GF(p^f) has order divisible by a
# primitive prime divisor of p^(f*k)-1.
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

end;

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
