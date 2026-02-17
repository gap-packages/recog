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



###################################################################################################
###################################################################################################
######## Constructive recognition SL(2,q) in natural representation ###############################
###################################################################################################
###################################################################################################



# TODO: Add MSLPs to these algorithms
# This algorithm is an implementation of the paper
# "Fast Recognition of Classical Groups over Large Fields"
# by Marston Conder and Charles Leedham-Green
RECOG.ConstructiveRecognitionSL2NaturalRepresentation := function(G, q, epsilon)  # TODO: never called
local F, factors, counter, one, factor, foundEle, passed, max, eigenvalues, eigenvalues2, eigenvectors, eigenvectors2, A, B, rand, foundConjugate, test, BDiag, C, basechange, v, d, CC, check, i, j, D, DD, T, S, o, t1, t2, zero, slp;

    factors := PrimeDivisors(q-1);
    counter := 1;
    F := GF(q);

    if not(IsObjWithMemory(GeneratorsOfGroup(G)[1])) then
        G := GroupWithMemory(G);
    fi;

    one := One(G);
    zero := Zero(F);
    max := Int(1/epsilon);
    while counter < max do

        # Step 1: Find random element of order q-1
        # foundEle := false;
        # while not(foundEle) do
        #    A := PseudoRandom(G);
        #    if A^(q-1) = one then
        #        passed := true;
        #        for factor in factors do
        #            if A^((q-1)/factor) = one then
        #                passed := false;
        #                break;
        #            fi;
        #        od;
        #        if passed then
        #            foundEle := true;
        #        else
        #            counter := counter + 1;
        #        fi;
        #    else
        #        counter := counter +1;
        #    fi;
        #    if counter >= max then
        #        return fail;
        #    fi;
        #od;

        # Step 1: Find random element of order q-1 (first improvement based on magma code)
        foundEle := false;
        while not(foundEle) do
            A := PseudoRandom(G);
            o := Order (A);
            if (o mod (q - 1) = 0) then
                A := A^(o/(q - 1));
                foundEle := true;
            else
                counter := counter +1;
            fi;
            if counter >= max then
                return fail;
            fi;
        od;

        # Step 2: Eigenvectors and eigenvalues
        eigenvalues := RootsOfPolynomial(CharacteristicPolynomial(A));
        # Note eigenvalues[1] = eigenvalues[2]^(-1)
        eigenvectors := [1,2];
        eigenvectors[1] := RECOG.EigenspaceMat(StripMemory(A), eigenvalues[1]);
        eigenvectors[2] := RECOG.EigenspaceMat(StripMemory(A), eigenvalues[2]);

        # Step 3: Conjugate of A that does not intersect with A's eigenspaces
        foundConjugate := false;
        eigenvectors2 := [1,2];
        while not(foundConjugate) do
            rand := PseudoRandom(G);
            B := A^rand;
            eigenvectors2[1] := RECOG.EigenspaceMat(StripMemory(B), eigenvalues[1]);
            eigenvectors2[2] := RECOG.EigenspaceMat(StripMemory(B), eigenvalues[2]);
            test := [];
            Append(test,eigenvectors[1]);
            Append(test,eigenvectors2[1]);
            if NullspaceMat(test) = [] then
                test := [];
                Append(test,eigenvectors[2]);
                Append(test,eigenvectors2[2]);
                if NullspaceMat(test) = [] then
                    basechange := [eigenvectors2[1,1],eigenvectors2[2,1]];
                    t1 := eigenvectors[1,1] * basechange^(-1);
                    t2 := eigenvectors[2,1] * basechange^(-1);
                    if (t1[1] <> zero) and (t1[2] <> zero) and (t2[1] <> zero) and (t2[2] <> zero) then
                        foundConjugate := true;
                    else
                        counter := counter + 1;
                    fi;
                else
                    counter := counter + 1;
                fi;
            else
                counter := counter + 1;
            fi;

            if counter >= max then
                return fail;
            fi;
        od;

        # Step 4: Find suitable C
        BDiag := IdentityMat(2,GF(q));
        BDiag[1,1] := eigenvalues[1];
        BDiag[2,2] := eigenvalues[2];
        v := eigenvectors[1,1] * basechange^(-1);
        d := v[2] * v[1]^-1;

        S := IdentityMat(2,F);
        while S = one do
            foundEle := false;
            while not(foundEle) do
                C := PseudoRandom(G);
                CC := basechange * C * basechange^(-1);
                if ((CC[1,2]-d*CC[1,1])) <> zero and ((d^2*CC[2,1] - d * CC[2,2]) <> zero) then
                    check := (d^2*CC[2,1] - d * CC[2,2])/(CC[1,2]-d*CC[1,1]);
                    if not(Zero(F) = check) and IsSquareFFE(F,check) then
                        i := LogFFE(check,eigenvalues[1])/2;
                        foundEle := true;
                    else
                        counter := counter + 1;
                    fi;
                else
                    counter := counter + 1;
                fi;

                if counter >= max then
                    return fail;
                fi;
            od;
            S := A^(-1) * (B^i*C)^(-1) * A * (B^i*C);
        od;

        # Step 5: Find suitable D
        v := eigenvectors[2,1] * basechange^(-1);
        d := v[2] * v[1]^-1;

        T := IdentityMat(2,F);
        while T = one do
            foundEle := false;
            while not(foundEle) do
                D := PseudoRandom(G);
                DD := basechange * D * basechange^(-1);
                if ((DD[1,2]-d*DD[1,1]) <> zero) and ((d^2*DD[2,1] - d * DD[2,2]) <> zero) then
                    check := (d^2*DD[2,1] - d * DD[2,2])/(DD[1,2]-d*DD[1,1]);
                    if not(Zero(F) = check) and IsSquareFFE(F,check) then
                        j := LogFFE(check,eigenvalues[1])/2;
                        foundEle := true;
                    else
                        counter := counter + 1;
                    fi;
                else
                    counter := counter + 1;
                fi;

                if counter >= max then
                    return fail;
                fi;
            od;
            T := A^(-1) * (B^j*D)^(-1) * A * (B^j*D);
        od;

        basechange := [eigenvectors[1,1],eigenvectors[2,1]];
        basechange[2] := basechange[2] * Determinant(basechange)^(-1);

        slp := SLPOfElms([A,S,T]);

        A := basechange * A * basechange^(-1);
        S := basechange * S * basechange^(-1);
        T := basechange * T * basechange^(-1);

        return [[A,S,T],basechange,slp];
    od;

    return fail;

end;



# Note that we use the discrete logarithm to normalise the primitive element at position [1,1]. But this is not necessarly as the entry at position [1,1] is primitive.
# Hence, this function can be adapted to larger fields by avoiding the normalisation step
RECOG.ConstructiveRecognitionSL2NaturalRepresentationCompleteBasis := function(list,F,q,p,f)  # TODO: never called
local w, k, Diag, coeffs, coeff, cong, t, s, SC, i, res, res2, A, S, T, upper, lower, basis, slp;

    list := GeneratorsWithMemory(list);

    A := list[1];
    S := list[2];
    T := list[3];

    # Normalisation step
    w := PrimitiveElement(F);
    k := LogFFE(w,A[1,1]);
    Diag := A^k;

    t := T[1,2];
    basis := [1..f];
    for i in [0..f-1] do
        basis[i+1] := w^(2*i);
    od;
    basis := Basis(F,basis);
    coeffs := Coefficients(basis,t^(-1));

    # standard basis element [1, 1, 0, 1]
    res := A^0;
    for i in [0..f-1] do
        coeff := Int(coeffs[i+1]);
        cong := Diag^(-i);
        res := res * ((T^(cong))^coeff);
    od;
    upper := [1..f];
    upper[1] := res;

    # set up complete basis for upper triangular matrices
    #UB := [GL(2, E) ! [1, x^(2 * i), 0, 1]: i in [0..e - 1]];
    #wUB := [wUS^(wD^-i): i in [0..e - 1]];
    for i in [1..f-1] do
        upper[i+1] := res^(Diag^(-i));
    od;

    s := S[2,1];
    coeffs := Coefficients(basis,s^(-1));

    # standard basis element [1, 0, 1, 1]
    res2 := A^0;
    for i in [0..f-1] do
        coeff := Int(coeffs[i+1]);
        cong := Diag^(i);
        res2 := res2 * ((S^(cong))^coeff);
    od;
    lower := [1..f];
    lower[1] := res2;

    # set up complete basis for lower triangular matrices
    for i in [1..f-1] do
        lower[i+1] := res2^(Diag^(i));
    od;

    slp := SLPOfElms(Concatenation([Diag],upper,lower));

    return [[Diag,upper,lower],slp];

end;


###################################################################################################
###################################################################################################
######## Rewriting SL(2,q) ########################################################################
###################################################################################################
###################################################################################################


# Note that we use the discrete logarithm to normalise the primitive element at position [1,1]. But this is not necessarly as the entry at position [1,1] is primitive.
# Hence, this function can be adapted to larger fields by avoiding the normalisation step
RECOG.RewritingSL2 := function(gens,F,q,p,f,ele)
local list, re, ell, mat, base, i, coeff, wMat, l1, l2, stdgens;

    stdgens := StripMemory(gens);
    stdgens := Concatenation([stdgens[1]],stdgens[2],stdgens[3]);
    stdgens := GeneratorsWithMemory(stdgens);
    l1 := stdgens{[2..f+1]};
    l2 := stdgens{[f+2..Size(stdgens)]};
    stdgens := [stdgens[1],l1,l2];

    base := [1..f];
    for i in [1..f] do 
        base[i] := (stdgens[2,i])[1,2];
    od;
    base := Basis(F,base);
    re := stdgens[1]^0;

    if ele[1,2] = Zero(F) then
        re := re*stdgens[2,1];
        mat := IdentityMat(2,F);
        mat[1,2] := One(F);
        ele := ele*mat;
    fi;

    if not(ele[1,1] = One(F)) then
        ell := (1-ele[1,1])*ele[1,2]^(-1);
        mat := IdentityMat(2,F);
        mat[2,1] := ell;
        ele := ele*mat;
        coeff := Coefficients(base,ell);
        wMat := stdgens[1]^0;
        for i in [1..f] do
            wMat := wMat*(stdgens[3,i])^Int(coeff[i]);
        od;
        re := re*wMat;
    fi;

    ell := -1*ele[1,2];
    mat := IdentityMat(2,F);
    mat[1,2] := ell;
    ele := ele*mat;
    coeff := Coefficients(base,ell);
    wMat := stdgens[1]^0;
    for i in [1..f] do
        wMat := wMat*(stdgens[2,i])^Int(coeff[i]);
    od;
    re := re*wMat;

    if not(ele[2,1] = Zero(F)) then
        ell := -1 * ele[2,1];
        mat := IdentityMat(2,F);
        mat[2,1] := ell;
        ele := mat*ele;
        coeff := Coefficients(base,ell);
        wMat := stdgens[1]^0;
        for i in [1..f] do
            wMat := wMat*(stdgens[3,i])^Int(coeff[i]);
        od;
        re := re*wMat;
    fi;

    return SLPOfElm(re^(-1));
end;



###################################################################################################
###################################################################################################
######## Constructive Recognition of SL(4,q) (Leedham-Green and O'Brien algorithm) ################
###################################################################################################
###################################################################################################



# Input: X where <X> is isomorphic to SL(4,q), F where X are dxd matrices over F_q = F (q = p^f prime power)
RECOG.OneEvenSL4 := function(X,F)
    local d, G, g, h, foundStrongInvoluation, order, gensCentraliser, EPlus;
    
    d := 4;
    G := GroupByGenerators(X);
    foundStrongInvoluation := false;
    while not(foundStrongInvoluation) do
        g := PseudoRandom(G);
        order := Order(g);
        if (order mod 2 = 0) then
            h := g^(order/2);
            EPlus := RECOG.FixspaceMat(h);
            if Size(EPlus) = 2 then
                foundStrongInvoluation := true;
            fi;
        fi;
    od;
    
    gensCentraliser := RECOG.InvolutionCentraliser(G,h,100);
    # TODO: Compute generating set for OmegaX(E) (see paper from LGO)

    #TODO: CONTINUE HERE

end;;



# Input: h an involuation in a BB group G, natural number N > 0
RECOG.InvolutionCentraliser := function(G, h, N)
    local C, i, g;

    C := [1..N];
    for i in [1..N] do
        g := PseudoRandom(G);
        C[i] := RECOG.ChFromg(h,g);
    od;

    return DuplicateFreeList(C);
end;;



# Input: h and g group elements of the same group. Returns an element as in Bray's Lemma
RECOG.ChFromg := function(h,g)
    local order, com;

    com := h^(-1)*g^(-1)*h*g;
    order := Order(com);
    
    if (order mod 2 = 0) then
        return com^(order/2);
    else
        return com^((order+1)/2)*g^(-1);
    fi;
end;;



###################################################################################################
###################################################################################################
######## Older algorithms #########################################################################
###################################################################################################
###################################################################################################



RECOG.RecogniseSL2NaturalOddCharUsingBSGS := function(g,f)
  local ext,p,q,res,slp,std;
  p := Characteristic(f);
  ext := DegreeOverPrimeField(f);
  q := Size(f);
  std := RECOG.MakeSL_StdGens(p,ext,2,2);
  slp := RECOG.FindStdGensUsingBSGS(g,std.all,false,true);
  if slp = fail then return fail; fi;
  res := rec( g := g, one := One(f), One := One(g), f := f, q := q,
              p := p, ext := ext, d := 2, bas := IdentityMat(2,f),
              basi := IdentityMat(2,f) );
  res.all := ResultOfStraightLineProgram(slp,GeneratorsOfGroup(g));
  res.s := res.all{[1..ext]};
  res.t := res.all{[ext+1..2*ext]};
  res.a := res.all[2*ext+1];
  res.b := res.all[2*ext+2];
  return res;
end;



RECOG.FindStdGensUsingBSGS := function(g,stdgens,projective,large)
  # stdgens generators for the matrix group g
  # returns an SLP expressing stdgens in the generators of g
  # set projective to true for projective mode
  # set large to true if we should not bother finding nice base points!
  local S,dim,gens,gm,i,l,strong;
  dim := DimensionOfMatrixGroup(g);
  if IsObjWithMemory(GeneratorsOfGroup(g)[1]) then
      gm := GroupWithMemory(StripMemory(GeneratorsOfGroup(g)));
  else
      gm := GroupWithMemory(g);
  fi;
  if HasSize(g) then SetSize(gm,Size(g)); fi;
  if large then
      S := StabilizerChain(gm,rec( Projective := projective,
        Cand := rec( points := One(g),
                     ops := ListWithIdenticalEntries(dim, OnLines) ) ) );
  else
      S := StabilizerChain(gm,rec( Projective := projective ) );
  fi;
  strong := ShallowCopy(StrongGenerators(S));
  ForgetMemory(S);
  l := List(stdgens,x->SiftGroupElementSLP(S,x));
  gens := EmptyPlist(Length(stdgens));
  for i in [1..Length(stdgens)] do
      if not l[i].isone then
          return fail;
      fi;
      Add(gens,ResultOfStraightLineProgram(l[i].slp,strong));
  od;
  return SLPOfElms(gens);
end;


###################################################################################################
###################################################################################################
######## Algorithm provided by Frank Lübeck #######################################################
###################################################################################################
###################################################################################################



####################   (c) 2025  Frank Lübeck   ##########################
##  
##  G must be SL(2,q) generated by 2x2 matrices over GF(q).
##  Returns [slps, mat] where slps is list of SLPs in given generators of G 
##  to elements which are conjugate by mat to standard/nice generators: 
##     t, u1, u2 = diag(1/Z(q),Z(q)) [[1,0],[1,1]], [[1,1],[0,1]]
##  
##  We construct elements with the strategy of Section 2. from the article
##    Conder, Leedham-Green, Fast recognition of classical groups
##    over large fields, Groups and Computation III, 2001.
##  and then adjust them to the form described above.
##  
##  Some comments:
##    - To find short SLP to the nice generators we avoid 'PseudoRandom(g)'
##      and instead just start with the trivial element and multiply random
##      generators to it.
##      This should be good enough because in both cases (element xm and twice
##      element cm in the code) almost half of the elements in G are suitable.
##  
##    - The list of SLPs in the result is probably what is needed for the
##      SLPforNiceGens for the RecogNode.
##  
##    - To find for a given element A in G an SLP in the nice generators compute
##       Astd := A^mat and use the function 'SLPinStandardSL2' from the file 
##       "SL2.g".
##    
##    - If q = 2^m with odd m then the computation of the eigenvalues of xm
##      needs the quadratic extension GF(2^(2m)).
##  
##  
##  Example (takes about 15 seconds on my notebook):
##      Size(SL(2,23^15));
##      G:=Group(List([1..4],i->PseudoRandom(SL(2,23^15))));
##      l:=RecogNaturalSL2(G,23^15);
##      nicegens:=List(l[1],a->ResultOfStraightLineProgram(a,GeneratorsOfGroup(G)));
##      List(last, a->a^l[2]);
##  

## Note does not work for q = 2,3,5
RecogNaturalSL2 := function(G, q)
  local GM, one, zero, qm1fac, c, m, gens, xm, x, pol, v, z, exp, a, 
        mat, tm, ym, y, ymat, tr, d, cm, r1, r2, r, log, i, trupm, 
        smm, trlowm, F, a2, bas, e, l, emax, tmp;
  GM := GroupWithMemory(G);
  one := One(G.1[1,1]);
  zero := Zero(one);
  
  # find element x of order q-1
  # (a power of x will become the nice generator t later)
  qm1fac := Factors(q-1);
  c := Product(Set(qm1fac));
  m := (q-1)/c;
  gens := GeneratorsOfGroup(GM);
  xm := One(GM);
  repeat 
    #xm := PseudoRandom(GM);
    xm := xm*Random(gens);
    x := StripMemory(xm);
    pol := [one, -x[1,1]-x[2,2], one];
    v := [zero, one];
    v := PowerModCoeffs(v, m, pol);
  until PowerModCoeffs(v, c, pol) = [one] and
            ForAll(qm1fac, p-> PowerModCoeffs(v, c/p, pol) <> [one]);
  # eigenvalues and eigenvectors of x (zeroes of pol)
  # we use Cantor-Zassenhaus
  z := Z(q);
  if q mod 2 = 0 then
    if q mod 3 = 1 then
      exp := (q-1)/3;
    else
      exp := (q^2-1)/3;
      z := Z(q^2);
    fi;
  else
    exp := (q-1)/2;
  fi;
  repeat
    v := [z^Random(0,q-1), one];
    v := PowerModCoeffs(v, exp, pol);
  until Length(v) = 2 and ValuePol(pol, (-v[1]+one)/v[2]) = zero;
  a := (-v[1]+one)/v[2];
  # colums of mat are eigenvectors for a and 1/a (x^mat is diagonal)
  mat := [[-x[1,2], -x[1,2]], [x[1,1]-a, x[1,1]-1/a]];
  if mat[1,1] = zero and mat[2,1] = zero then
    mat[1,1] := x[2,2]-a; mat[2,1] := -x[2,1];
  fi;
  if mat[1,2] = zero and mat[2,2] = zero then
    mat[1,2] := x[2,2]-1/a; mat[2,2] := -x[2,1];
  fi;


  # find conjugate of x with different eigenspaces
  # (almost all conjugates will do)
  tm := One(GM);
  repeat
    tm := tm * Random(gens);
    ym := tm*xm*tm^-1;
    y := StripMemory(ym);
    ymat := y*mat;
  until ymat[1,1]*mat[2,1]-ymat[2,1]*mat[1,1] <> zero and
        ymat[1,2]*mat[2,2]-ymat[2,2]*mat[1,2] <> zero;
  # now y^(tm * mat) = diag(a, a^-1) 
  tr := tm*mat;

  # a-eigenvector of x in new basis
  d := tr^-1 * [mat[1,1],mat[2,1]];
  # can be scaled to [1,d]
  d := d[2]/d[1];
  cm := One(GM);
  repeat
    # look for cm with non-trivial conditions (i <> 0, (q-1)/2)
    repeat 
      cm := cm*Random(gens);
      c := StripMemory(cm)^tr;
      r1 := c[2,1]+d*c[2,2];
      r2 := d^2*c[1,2]+d*c[1,1];
    until r2 <> zero and r1 <> zero and r1 <> r2 and r1 <> -r2;;
    r := r1 / r2;
    log := DLog(a, r, qm1fac);
    i := false;
    if log mod 2 = 0 then
      i := log/2;
    elif q mod 2 = 0 then
      i := (q-1-log)/2;
    fi;
    if IsInt(i) then
      # this will in most cases be a transvection normalized by x
      trupm := Comm(xm, ym^i*cm);
      smm := trupm^mat;
      if smm[1,2] = zero then
        i := false;
      else
        # rescale first column of mat such that trupm^mat = [[1,1],[0,1]]
        mat[1,1] := mat[1,1]*smm[1,2];
        mat[2,1] := mat[2,1]*smm[1,2];
        tr := tm*mat;
      fi;
    fi;
  until IsInt(i);

  # same for the other eigenvector of x:
  # 1/a-eigenvector of x in new basis
  d := tr^-1 * [mat[1,2],mat[2,2]];
  # can be scaled to [1,d]
  d := d[2]/d[1];
  cm := One(GM);
  repeat
    # look for cm with non-trivial conditions (i <> 0, (q-1)/2)
    repeat 
      cm := cm*Random(gens);
      c := StripMemory(cm)^tr;
      r1 := c[2,1]+d*c[2,2];
      r2 := d^2*c[1,2]+d*c[1,1];
    until r2 <> zero and r1 <> zero and r1 <> r2 and r1 <> -r2;;
    r := r1 / r2;
    log := DLog(a, r, qm1fac);
    i := false;
    if log mod 2 = 0 then
      i := log/2;
    elif q mod 2 = 0 then
      i := (q-1-log)/2;
    fi;
    if IsInt(i) then
      # in most cases a transvection which becomes conjugated by mat
      # lower triangular (here it is more difficult to rescale such 
      # that the conjugate matrix is [[1,0],[1,1]]).
      trlowm := Comm(xm, ym^i*cm);
      smm := trlowm^mat;
      if smm[2,1] = zero then
        i := false;
      fi;
    fi;
  until IsInt(i);

  # adjust lower left entry of trlowm^mat to one
  # (we use F_p linear algebra in F_q to find the nice element
  # of products of trlowm^(x^i) for some small i)
  if smm[2,1] <> one then
    F := GF(q);
    a2 := a^2;
    bas := [smm[2,1]];
    e := DegreeOverPrimeField(F);
    for i in [1..e-1] do
      Add(bas, bas[i]*a2);
    od;
    bas := Basis(F, bas);
    l := List(Coefficients(bas, one), IntFFE);
    emax := e;
    while l[emax] = 0 do
      emax := emax-1;
    od;
    tmp := trlowm;
    if l[1] = 0 then
      trlowm := One(GM);
    else
      trlowm := tmp^l[1];
    fi;
    for i in [2..emax] do
      tmp := tmp^xm;
      if l[i] <> 0 then
        trlowm := trlowm*tmp^l[i];
      fi;
    od;
  fi;

  # finally power x to change a to 1/Z(q)
  if a <> 1/Z(q) then
    log := DLog(a, 1/Z(q), qm1fac);
    xm := xm^log;
  fi;

  # return SLPs of elements mapped by mat to 
  # diag(1/Z(q),Z(q))[[1,0],[1,1]], [[1,1],[0,1]],
  # and mat
  return [List([xm, trlowm, trupm], SLPOfElm), mat];
end;

## The following code is provided by Till Eisenbrand.
## It integrates the algorithm above to produce the same output format
## as RECOG.RecogniseSL2NaturalEvenChar and
## RECOG.RecogniseSL2NaturalOddCharUsingBSGS.
## G must be SL(2,q) generated by 2x2 matrices over GF(q).
RECOG.ConRecogNaturalSL2 := function(G, f)
  local q, res, nicegens, diag, u1, u2, umat, lmat, k, j, i, el, result, bas, true_diag, true_u1, true_u2, basi, p, basis, coeffs, m, c, l, a, b;
  q := Size(f);
  p := Characteristic(f);
  j := DegreeOverPrimeField(GF(q));

  ## if q = 2,3,5 then RecogNaturalSL2 does not work
  if q = 2 then
    return RECOG.RecogniseSL2NaturalEvenChar(G,f,false);
  fi;
  if q = 3 or q = 5 then
    return RECOG.RecogniseSL2NaturalOddCharUsingBSGS(G,f);
  fi;
  ## standard generators of SL(2,q) in the natural representation
  true_diag  := [[Z(q)^(-1),0*Z(q)],[0*Z(q),Z(q)]];
  true_u1 := [[Z(q)^0,0*Z(q)],[Z(q)^0,Z(q)^0]];
  true_u2 := [[Z(q)^0,Z(q)^0],[0*Z(q),Z(q)^0]];
  ## retry until RecogNaturalSL2 returns generators matching the standard form
  ## TODO: Perhaps remove this for-loop
  for i in [1..100] do
    res := RecogNaturalSL2(G,q);
    nicegens :=List(res[1],a->ResultOfStraightLineProgram(a,GeneratorsOfGroup(G)));
    diag := nicegens[1];
    u1 := nicegens[2];
    u2 := nicegens[3];
    ## check if we found the correct generators
    if diag^res[2] = true_diag and u1^res[2] = true_u1 and u2^res[2] = true_u2 then 
      break; 
    fi;
  od;

  if IsEvenInt(q) then
    ## even characteristic: conjugation by diag generates all of GF(q)* directly
    lmat := [];
    for k in [0..j-1] do
      i := (q-1-k)*Int(2)^-1 mod (q-1);
      el := u1^(diag^i);
      Add(lmat,el);
    od;
    umat := [];
    for k in [0..j-1] do
      i := k * Int(2)^-1 mod (q-1);
      el := u2^(diag^i);
      Add(umat, el);
    od;
  else
    ## odd characteristic: conjugation only yields squares, so express z^l
    ## in the Fp-basis {z^0, z^2, ..., z^(2(j-1))} and multiply conjugates
    ## TODO: Perhaps create the lower/upper matrices with z^0, z^2, ..., z^(2(j-1)) 
    ##       as entries instead of z^0, z^1, ..., z^(j-1)
    basis := List([0..j-1], i -> Z(q)^(2*i));
    lmat := [];
    for l in [0..j-1] do
      coeffs := Coefficients(Basis(GF(q), basis), Z(q)^l);
      m := u1^0;
      for i in [0..j-1] do
        c := IntFFE(coeffs[i+1]);
        m := m * (diag^i * u1 * diag^(-i))^c;
      od;
      Add(lmat, m);
    od;
    umat := [];
    for l in [0..j-1] do
      coeffs := Coefficients(Basis(GF(q), basis), Z(q)^l);
      m := u2^0;
      for i in [0..j-1] do
        c := IntFFE(coeffs[i+1]);
        m := m * (diag^(-i) * u2 * diag^i)^c;
      od;
      Add(umat, m);
    od;
  fi;
  basi := res[2];
  bas := basi^(-1);
  a := umat[1]^(-1)*lmat[1]*umat[1]^(-1);
  b := One(umat[1]);
  result :=  rec( g := G, t := lmat, s := umat, bas := bas, basi := basi,
                one := One(f), a := a, b := b, 
                all := Concatenation(umat,lmat,[a],[b]), One := One(umat[1]), f := f,
                q := q, p := Characteristic(f), ext := j, d := 2 );
  return result;
end;


## test function: compares ConRecogNaturalSL2 against the built-in recognition
## note: does not work for q = 2, 3, 5
## Input: either a list of prime powers or the empty list 
## (then a preset list of prime powers is tested).
test_ConRecogNaturalSL2 := function(input)
  local i, G, list, qlist, res_old, res, f, q, valid;
  if input = [] then
    qlist := [2^3, 2^5, 3^4, 25, 17^3, 9967]; 

  elif Size(input)>0 then
    qlist := [];
    for q in input do
      if IsPrimePowerInt(q) then
        Add(qlist, q);
      fi;
    od;
  fi;
  
  valid := true;
  for q in qlist do
    Print("testing q = ", q, "\n");
    f := GF(q);
    list := [];
    for i in [1..5] do
      Add(list, Random(SL(2,q)));
    od;
    G := GroupWithGenerators(list);
    if IsEvenInt(q) then
      res_old := RECOG.RecogniseSL2NaturalEvenChar(G,f,false);
    else
      res_old := RECOG.RecogniseSL2NaturalOddCharUsingBSGS(G,f);
    fi;
    res := RECOG.ConRecogNaturalSL2(G,f);
    ## compare all generators after change of basis
    for i in [1..Length(res.all)] do
      if res.all[i]^res.basi <> res_old.all[i]^res_old.basi then
        Print("Test failed for q = ", q, ", index i = ", i, " in the list \"all\" failed\n");
          valid := false;
      fi;
    od;
  od;
  if valid then
    Print("All tests passed.\n");
  fi;
end;


