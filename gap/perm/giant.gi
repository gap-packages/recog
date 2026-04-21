#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This files's authors include Maska Law, Ákos Seress.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
##
##  This file provides code for recognising whether a permutation group
##  on n points is isomorphic to A_n or S_n acting naturally.
##
#############################################################################

DeclareInfoClass( "InfoGiants" );
SetInfoLevel( InfoGiants, 1 );

#########################################################################
## For a permutation group grp on n points and a list lenList of integers,
## returns either a list cycList of equal length such that cycList[i] is a
## cycle of length lenList[i] for all 1 <= i <= Length(lenList), or fail.
## Each entry of lenList must be either a prime number or n or n-1. Further,
## each entry must be at least 2.
## The desired cycles are found by a random search, drawing at most N random
## elements from grp.
## Thus if grp actually contains cycles of the desired shape, then the function
## succeeds with a probability that grows as N grows.
RECOG.FindCycles := function ( grp, lenList, N )

    local mp, n, cycList, rand, cyclen, i, k, orders, finished;

    mp := MovedPoints(grp);
    n := Length(mp);
    cycList := [];

    finished := false;
    while N > 0 and not finished do
        N := N - 1;
        rand := PseudoRandom( grp );
        # If cyclen[i] is bound, it is the number of cycles of length i+1 in rand.
        # Otherwise rand has no cycle of length i+1.
        cyclen := CycleStructurePerm(rand);
        # If `finished` is not changed to false in the following loop, then we are done
        finished := true;
        for i in [1..Length(lenList)] do
            if not IsBound(cycList[i]) then # no cycle of desired length has been found yet
                k := lenList[i];
                # Check that rand contains exactly one cycle of length k and
                # no cycle whose length is a proper multiple of k
                if IsBound(cyclen[k-1]) and cyclen[k-1] = 1 then
                    if k = n-1 or k = n then
                        # The existence of a full cycle in rand guarantees that
                        # rand is equal to this full cycle.
                        cycList[i] := rand;
                    else
                        # set orders to the list of all l>=2 such that rand contains an l-cycle and
                        #  l<>k. Since rand contains a k-cycle, we only have to check up to n-k.
                        orders := Filtered([2..n-k],x->IsBound(cyclen[x-1]) and x<>k);
                        if ForAll(orders, x->(x=k) or (x mod k <> 0)) then
                            if IsEmpty(orders) then
                                cycList[i] := rand; # rand is a k-cycle
                            else
                                # Raising to the power of Lcm(orders) kills all cycles of rand
                                # whose length is not k. Further, the condition that k
                                # is a prime guarantees that every non-trivial power of
                                # a k-cycle is a k-cycle. Thus rand^(Lcm(orders))
                                # is a k-cycle.
                                cycList[i] := rand^(Lcm(orders));
                            fi;
                        fi;
                    fi;
                fi;
                if not IsBound(cycList[i]) then
                    finished := false;
                fi;
            fi;
        od;
    od;

    if finished then
        return cycList;
    else
        return fail;
    fi;
end;

#######################################################################
##
#F  NiceGeneratorsSn(<grp>,<N>) ...... find n-cycle, transposition
##
## For a permutation group grp on n points, this function returns either fail
## or a list [ fullCycle, transp ] such that the following hold:
## - n > 2.
## - fullCycle is an n-cycle.
## - transp is a transposition, i.e., a 2-cycle.
## - transp interchanges two successive points of fullCycle. In other words,
##   fullCycle = (1,...,n) and transp = (1,2) up to renaming the n points.
## The conditions on [ fullCycle, transp ] imply that grp is the full symmetric
## group on n points. Thus the function always returns fail if grp is not the
## full symmetric group, and also if n <= 2.
## fullCycle, transp are found by a random search, drawing at most N random
## elements from grp.
## Thus if grp is the full symmetric group on n points, then the function does not
## return fail with a probability that grows as N grows.

RECOG.NiceGeneratorsSn := function ( grp, N )

    local cyclen, fullCycle, transp, rand, orders, i, supp, suppNew, n, mp,
        numTries, cycles;

    mp := MovedPoints(grp);
    n := Length(mp);

    if n<=2 then
        return fail;
    fi;

    # Random search for an n-cycle and a transposition in grp
    cycles := RECOG.FindCycles(grp, [2, n], N);
    if cycles = fail then
        return fail;
    fi;
    fullCycle := cycles[2];
    transp := cycles[1];

    # Conjugate transp by random elements until we obtain a transposition that
    # interchanges successive elements of fullCycle.
    numTries := 10*n; # TODO: Why do we choose this constant?
    supp := MovedPoints( transp ); # Support of transp
    while numTries > 0 do
        numTries := numTries-1;
        rand := PseudoRandom( grp );
        suppNew := List(supp, x->x^rand); # Support of transp^rand
        # Check that transp^rand interchanges successive points of fullCycle,
        # or equivalently, that fullCycle moves one point of transp^rand
        # to the other one.
        if suppNew[1]^fullCycle = suppNew[2]
            or suppNew[2]^fullCycle = suppNew[1]
        then
            return [ fullCycle, transp^rand ];
        fi;
    od;

    return fail;

end;


######################################################################
##
#F  ConjEltSn(<grp>,<fullCycle>,<transp>)
##
##
## For a permutation group grp and elements fullCycle, transp that satisfy the conditions
## of NiceGeneratorsSn, returns a permutation conj such that 
## fullCycle^conj = (1,...,n) and transp^conj=(1,2).
## The permutation conj lies in SymmetricGroup(la) where la is the largest moved point
## of grp. However, conj need not lie in grp (e.g. if 1 is not a moved point of grp).
RECOG.ConjEltSn :=  function( grp, fullCycle, transp )

    local c,i,la,n,rest,pos1,nextPos,suppTransp,mp;

    mp := MovedPoints(grp); # = MovedPoints(fullCycle)
    n := Length(mp);
    la := mp[n];   # this is the largest moved point

    suppTransp := MovedPoints( transp );

    # Define pos1 to be the unique element of suppTransp that is mapped by fullCycle
    # to the other element of suppTransp.
    # Thus pos1 must be mapped to 1 by conj, and the other element of suppTransp is mapped to 2.
    if suppTransp[1]^fullCycle = suppTransp[2] then
        pos1 := suppTransp[1];
    else
        pos1 := suppTransp[2];
    fi;

    ## We construct a list c that defines the desired permutation conj
    c := [];
    # conj maps the elements of mp bijectively to [1..n], in the order prescribed by fullCycle.
    # In particular, it maps pos1, pos1^fullCycle to 1, 2.
    nextPos := pos1;
    for i in [ 1 .. n ] do
        c[nextPos] := i;
        nextPos := nextPos^fullCycle;
    od;
    # The remaining points in [1..la] must be mapped bijectivey to [n+1..la] to ensure that
    # conj is a permutation. However, the precise values of individual points are irrelevant.
    rest := Difference([1..la],mp);
    for i in [1..Length(rest)] do
        c[rest[i]] := i+n;
    od;

    return PermList( c );

end;


########################################################################
##
#F  NiceGeneratorsAnEven(<grp>,<N>) . .
##
##
## For a permutation group grp on n points, this function returns either fail
## or a list [ longPerm, cyc3 ] such that the following hold:
## - n > 3 and n is even.
## - longPerm is the product of a 2-cycle and an (n-2)-cycle that are disjoint.
## - cyc3 is a 3-cycle.
## - The support of the 2-cycle in longPerm is contained in the support of cyc3.
##   In other words, longPerm = (1,2)(3,...,n) and cyc3=(1,2,3) up to renaming
##   the n points.
## The conditions on [ longPerm, cyc3 ] imply that grp contains the full alternating
## group on n points. Thus the function always returns fail if grp does not contain the
## full alternating group, and also if n <= 3.
## long, cyc3 are found by a random search, drawing at most N random
## elements from grp.
## Thus if grp contains the full alternating group on an even number of points, then the
## function succeeds with a probability that grows as N grows.

RECOG.NiceGeneratorsAnEven := function ( grp, N )

    local mp, fp, supp3, others, n, cycles, cyc3, cyc3New, cycNm1, numTries, rand, a, b;

    mp := MovedPoints(grp);
    n := Length(mp);

    # Random search for an (n-1)-cycle (not an (n-2)-cycle!) and a 3-cycle
    cycles := RECOG.FindCycles(grp, [3, n-1], N);
    if cycles = fail then
        return fail;
    fi;
    cyc3 := cycles[1]; # 3-cycle
    cycNm1 := cycles[2]; # (n-1)-cycle ("Nm1" = "n minus 1")

    # Random search for a permutation rand such that the support of
    # cyc3^rand contains the fixed point of cycNm1
    numTries := 10*n; # TODO: Why do we choose this constant?
    fp := Difference( mp, MovedPoints(cycNm1) )[1]; # Fixed point of cycNm1
    supp3 := MovedPoints( cyc3 ); # Support of cyc3
    while numTries > 0 do
        numTries := numTries-1;
        rand := PseudoRandom( grp );
        if fp in List( supp3, x -> x^rand ) then # if fp in support of cyc3^rand
            cyc3 := cyc3^rand; # We found the desired 3-cycle
            # Define points a,b such that cyc3 = (fp, a, b)
            a := fp^cyc3;
            b := a^cyc3;
            # Define a new 3-cycle cyc3New of the form (fp, c, d) for points c,d with c^cycNm1=d
            if a^cycNm1 = b then
                cyc3New := cyc3; 
            elif b^cycNm1 = a then
                cyc3New := cyc3^2; # = (fp, b, a)
            else
                # In this case, g := cyc3^cycNm1 has the form (fp, p, q)
                # where {p=a^cycNm1,q^cycNm1} is disjoint from {a,b}. Hence
                # [g,cyc3] = g^-1 g^cyc3 = (fp,q,p) (a,p,q)=(fp,a,p).
                cyc3New := Comm(cyc3^cycNm1,cyc3);
            fi;
            # Rename points so that fp=1, c=2, d=3, cycNm1=(2,...,n). Then
            # cyc3New = (1,2,3), cycNm1*cyc3New=(2,...,n)*(1,2,3)=(1,2)(3,...,n).
            return [ cycNm1 * cyc3New, cyc3New ];
        fi;
    od;
    return fail;
end;

#########################################################################
##
#F  NiceGeneratorsAnOdd(<grp>,<N>) . . . . find (n-2)-cycle, 3-cycle
##
##
## For a permutation group grp on n points, this function returns either fail
## or a list [ longCycle, shortCycle ] such that the following hold:
## - n > 4 and n is odd.
## - longCycle is an (n-2)-cycle.
## - shortCycle is a 3-cycle.
## - The supports of longCycle and shortCycle intersect in a single point. In
##   other words, longCycle = (3,...,n) and shortCycle=(1,2,3) up to renaming
##   the n points.
## The conditions on [ longCycle, shortCycle ] imply that grp contains the full alternating
## group on n points. Thus the function always returns fail if grp does not contain the
## full alternating group, and also if n <= 4.
## longCycle, shortCycle are found by a random search, drawing at most N random
## elements from grp.
## Thus if grp contains the full alternating group on an odd number of points, then the
## function does not return fail with a probability that grows as N grows.

RECOG.NiceGeneratorsAnOdd := function ( grp, N )

    local cyclen, cycN, cyc3, cyc3Cons, cyc3New, cyc3NewNew, rand, supp3, supp3New, 
        supp3NewShifted, numConsecutives, cycles, numTries, n;

    n := Length(MovedPoints(grp));

    # Random search for an n-cycle (not an (n-2)-cycle!) and a 3-cycle
    cycles := RECOG.FindCycles(grp, [3, n], N);
    if cycles = fail then
        return fail;
    fi;
    cyc3 := cycles[1]; # 3-cycle
    cycN := cycles[2]; # n-cycle

    # Random search for cyc3Cons, a 3-cycle that moves 3 consecutive points of cycN.
    # In the following comments, we assume that the points in mp are renamed
    # so that cycN = (1,...,n). We look for a cycle of the form (i,i+1,i+2) (mod n).
    numTries := 10*n; # TODO: Why do we choose this constant?
    supp3 := MovedPoints( cyc3 );
    cyc3Cons := fail;
    while numTries > 0 and cyc3Cons = fail do
        numTries := numTries-1;
        rand := PseudoRandom( grp );
        # support of cyc3New:=cyc3^rand, say [i,j,k].
        # We will compute cyc3New only later because we might not need it.
        supp3New := List( supp3, x -> x^rand );
        # support of cyc3New^cycN, so [i,j,k]^cycN=[i+1,j+1,k+1] (mod n)
        supp3NewShifted := List( supp3New, x -> x^cycN );
        # Number of p \in [i,j,k] s.t. p+1 \in [i,j,k] (mod n)
        numConsecutives := Length( Intersection( supp3New, supp3NewShifted ) );
        if numConsecutives = 2 then
            # In this case, {i,j,k} = {p,p+1,p+2} for some p.
            # Thus cyc3New is either (p,p+1,p+2) or (p,p+2,p+1) (mod n).
            cyc3New := cyc3^rand;
            if ForAny(supp3New, x->x^cycN=x^cyc3New) then
                # In this case, cyc3New = (p,p+1,p+2) (mod n).
                # I.e. cyc3New moves points in same order as cycN.
                cyc3Cons := cyc3New;
            else
                # In this case, cyc3New = (p,p+2,p+1) (mod n).
                cyc3Cons := cyc3New^2; # = cyc3New^-1
            fi;
        elif numConsecutives = 1 then
            # In this case, {i,j,k}={p,p+1,q} (mod n) for some p,q
            # with q not in [p-1,p+2] (mod n).
            # Again, cyc3New is either (p,p+1,q) or (p,q,p+1) (mod n).
            cyc3New := cyc3^rand;
            # We define cyc3NewNew to be (p,p+1,q):
            if ForAny(supp3New, x->x^cycN=x^cyc3New) then
                # In this case, cyc3New = (p,p+1,q) (mod n)
                cyc3NewNew := cyc3^rand;
            else
                # In this case, cyc3New = (p,q,p+1) (mod n)
                cyc3NewNew := (cyc3^rand)^2;
            fi;
            cyc3Cons := Comm( cyc3NewNew^2, cyc3NewNew^cycN );
            # = cyc3NewNew^-2 * (cyc3NewNew^2)^(cyc3NewNew^cycN)
            # = (p,p+1,q)*(p,q,p+2) = (p,p+1,p+2)
        fi;
    od;

    if cyc3Cons <> fail then
        # cycN * cyc3Cons^2 = (1,...,n)*(p,p+2,p+1)=(1,...,p-1,p+2,p+3,...,n)
        # = (n-2)-cycle whose support intersects [p,p+1,p+2] in one point.
        return [ cycN * cyc3Cons^2, cyc3Cons];
    else
        return fail;
    fi;
end;


#########################################################################
##
#F  ConjEltAnEven(<grp>,<longPerm>,<cyc3>)
##
##
## For a permutation group grp and elements longPerm, cyc3 that satisfy the conditions
## of NiceGeneratorsAnEven, returns a permutation conj such that 
## longPerm^conj = (1,2)(3,...,n) and cyc3^conj=(1,2,3).
## The permutation conj lies in SymmetricGroup(la) where la is the largest moved point
## of grp. However, conj need not lie in grp (e.g. if 1 is not a moved point of grp).

RECOG.ConjEltAnEven := function( grp, longPerm, cyc3 )
    local c,i,la,n,rest,pos,s1,s1lo,supp3,mp,p1,p2,p3;

    mp := MovedPoints(grp);
    n := Length(mp);
    la := mp[n];    # this is the largest moved point

    # In the following, we denote by p1,p2,p3 the three points s.t. cyc3=(p1,p2,p3)
    # and p1^longPerm=p2, p2^longPerm=p1.
    # conj should map p1 to 1, p2 to 2, 3 to 3.
    supp3 := MovedPoints(cyc3);  # = {p1,p2,p3} as a set, but not necessarily as a list

    ## Identify which point in supp3 is p1, which one is p2, which one is p3.
    # Note: p1 is the unique p in supp3 with p^longPerm=p^cyc3.
    s1 := supp3[1];
    s1lo := s1^longPerm;
    if s1lo in supp3 then # if {s1,s1lo} = {p1,p2}
        if s1^cyc3 = s1lo then # if [s1,s1lo] = [p1,p2]
            p1 := s1;
            p2 := s1lo;
        else
            p1 := s1lo;
            p2 := s1;
        fi;
    else   # if s1 = p3
        if supp3[2]^cyc3 = supp3[2]^longPerm then # if supp3[2] = p1
            p1 := supp3[2];
            p2 := supp3[3];
        else
            p1 := supp3[3];
            p2 := supp3[2];
        fi;
    fi;

    ## Construct a list c that defines the permutation conj.
    c := [];
    c[p1] := 1;
    c[p2] := 2;
    pos := Difference(supp3,Set([p1,p2]))[1]; # = p3
    for i in [3..n] do
        c[pos] := i;
        pos := pos^longPerm;
    od;
    # The remaining points in [1..la] must be mapped bijectivey to [n+1..la] to ensure that
    # conj is a permutation. However, the precise values of individual points are irrelevant.
    rest := Difference([1..la],mp);
    for i in [1..Length(rest)] do
        c[rest[i]] := i+n;
    od;

    return PermList( c );

end;


######################################################################
##
#F  ConjEltAnOdd(<grp>,<longCycle>,<shortCycle>)
##
##
## For a permutation group grp and elements longCycle, shortCycle that satisfy the conditions
## of NiceGeneratorsAnOdd, returns a permutation conj such that 
## longCycle^conj = (3,...,n) and shortCycle^conj=(1,2,3).
## The permutation conj lies in SymmetricGroup(la) where la is the largest moved point
## of grp. However, conj need not lie in grp (e.g. if 1 is not a moved point of grp).

RECOG.ConjEltAnOdd := function( grp, longCycle, shortCycle )
    local c,compt,i,la,n,rest,pos,mp;

    mp := MovedPoints(grp);
    n := Length(mp);
    la := mp[n];   # this is the largest moved point

    # compt is the common point moved by both longCycle and shortCycle.
    # It is mapped to 3 by conj.
    compt := Intersection( MovedPoints( longCycle ), MovedPoints( shortCycle ) )[1];
    
    ## Construct a list c that defines the permutation conj.
    c := [];
    # The points in MovedPoints(shortCycle) \ {compt} are mapped to 1 and 2.
    c[ compt^shortCycle ] := 1;
    c[ (compt^shortCycle)^shortCycle ] := 2;
    # The points in MovedPoints(longCycle) are mapped to 3,...,n
    pos := compt;
    for i in [3..n] do
        c[pos] := i;
        pos := pos^longCycle;
    od;
    # The remaining points in [1..la] must be mapped bijectivey to [n+1..la] to ensure that
    # conj is a permutation. However, the precise values of individual points are irrelevant.
    rest := Difference([1..la],mp);
    for i in [1..Length(rest)] do
        c[rest[i]] := i+n;
    od;

    return PermList(c);

end;


######################################################################
##
#F  RecogniseGiant(<grp>, <eps>) . . . . . . recognition function
##
##
##  This is the main function.
##  For a permutation group grp, returns either fail or a record with the following entries:
##  - stamp: either "Sn" or "An".
##  - degree: An integer such that grp is isomorphic (as a permutation group) to
##    S_degree if stamp="Sn" and to A_degree if stamp="An"
##  - conjPerm: A permutation such that x -> x^conj is an isomorphism from grp to
##    S_degree or A_degree
##  - gens: Nice generators of grp. That is, the images of the following permutations
##    under the isomorphisms described above:
##    - (1,2), (1,...,degree) if stamp="Sn"
##    - (1,2,3), (1,2)(3,...,degree) if stamp="An" and degree is even
##    - (1,2,3), (3,...,degree) if stamp="An" and degree is odd
##  The recognition is performed by a random search with threshold eps>0.
##  The smaller eps is, the longer we search before we give up.
##  TODO: Can we give more details on the threshold eps? Does it come from a specific paper?
##

RECOG.RecogniseGiant :=  function( grp, eps )

    local le, N, gens, conj, n, conjFunc, grpName, infoString, mp;

    mp := MovedPoints(grp);
    n := Length(mp);

    # Define le to be the smallest integer such that 2^le >= eps^-1
    le := 0;
    while 2^le < eps^-1 do
        le := le + 1;
    od;

    # TODO: Document these magic constants. They are probably from some paper.
    # Further, Max Horn suggested that it may be better to use a smaller N.
    N := Int(24 * (4/3)^3 * le * 6 * n);

    # If grp contains any element of negative sign, we try to recognise Sn, otherwise An.
    # Recognition succeeds if and only if gens <> fail.
    if ForAny(GeneratorsOfGroup( grp ), x -> SignPerm(x) = -1) then
        gens := RECOG.NiceGeneratorsSn( grp, N );
        conjFunc := RECOG.ConjEltSn;
        grpName := "Sn";
    else
        grpName := "An";
        if n mod 2 = 0 then
            gens := RECOG.NiceGeneratorsAnEven( grp, N );
            conjFunc := RECOG.ConjEltAnEven;
        else
            gens := RECOG.NiceGeneratorsAnOdd( grp, N );
            conjFunc := RECOG.ConjEltAnOdd;
        fi;
    fi;

    if gens = fail then
        infoString := Concatenation("couldn't find nice generators for ", grpName);
        Info(InfoGiants,1,infoString);
        return fail;
    fi;

    conj := conjFunc( grp, gens[1], gens[2] );

    return rec( stamp := grpName, degree := n,
                gens := Reversed(gens),  conjperm := conj );
end;


########################################################################
##
#F  FindHomomorphismMethods.Giant
##

# See Corollary 10.2.2 in [Ser03].
# See also `DoSnAnGiantTest` in the GAP library which seems to be a
# close variant of this code.
RECOG.IsGiant:=function(g,mp)
  local bound, i, p, cycles, l, x, n;
  n := Length(mp);
  bound:=20*LogInt(n,2);
  i:=0;
  repeat
    i:=i+1;
    p:=PseudoRandom(g);
    x:=Random(mp);
    l:=CycleLength(p,x);
  until (i>bound) or (l> n/2 and l<n-2 and IsPrime(l));
  if i>bound then
    return fail;
  else
    return true;
  fi;
end;

##  SLP for pi from (1,2), (1,...,n)

RECOG.SLPforSn :=  function( n, pi )

    local cycles, initpts, c, newc, i, R, ci, cycslp, k ;

    if IsOne(pi) then
        return StraightLineProgramNC( [[1,0]], 2 );
    fi;
    if LargestMovedPoint(pi) > n then
        return fail;
    fi;

    # we need the cycles of pi of length > 1 to be written such
    # that the minimum point is the initial point of the cycle
    initpts := [ ];
    cycles := [ ];
    for c in Filtered( Cycles( pi, [ 1 .. n ] ), c -> Length(c) > 1 ) do
        i := Minimum( c );
        Add( initpts, i );
        if i = c[1] then
            Add( cycles, c );
        else
            newc := [ i ];
            for k in [ 2 .. Length(c) ] do
                Add( newc, newc[k-1]^pi );
            od;
            Add( cycles, newc );
        fi;
    od;

    # R will be a straight line program from tau_1, sigma_1
    # we update cycle product, tau_i+1, sigma_i+2
    # and then overwrite the updates into positions 1,2,3
    R := [ [1,0], [3,1], [1,1], [2,1,1,1],
                    [[4,1],1], [[5,1],2], [[6,1],3] ];
    i := 1;
    repeat
        if i in initpts then
            # ci is the cycle of pi beginning with i
            ci := cycles[ Position( initpts, i ) ];
            # cycslp is the SLP for ci from tau_i and sigma_i+1
            cycslp := [ 1,1, 3,1+ci[1]-ci[2] ];
            for k in [ 2 .. Length(ci)-1 ] do
                Append( cycslp, [ 2,1, 3,ci[k]-ci[k+1] ] );
            od;
            Append( cycslp, [ 2,1, 3,Last(ci)-ci[1]-1 ] );
            Append( R, [ [cycslp,4] ]);
        else    # we carry forward cycle product computed so far
            Append( R, [ [[1,1],4] ] );
        fi;
                # we update tau_i+1 and sigma_i+2
        Append( R, [ [[2,1,3,-1,2,1,3,1,2,1],5],
                 [[3,1,2,1,3,-1,2,1,3,1,2,1],6],
                [[4,1],1], [[5,1],2], [[6,1],3] ]);
        i := i + 1;
    until i > Maximum( initpts );

    # the return value
    Add(R,[ [1,1],1 ]);

    # R is a straight line program with 2 inputs
    R:=StraightLineProgramNC( R, 2 );

    return R;

end;


##  SLP for pi from (1,2,3), sigma

RECOG.SLPforAn :=  function( n, pi )

    local cycles, initpts, c, newc,  R, i, nexttrpn, ci, cycslp, k, j,
          nexttau, nextsigma ;

    if IsOne(pi) then
        return StraightLineProgramNC( [[1,0]], 2 );
    fi;
    if SignPerm( pi ) = -1 then
        return fail;
    fi;
    if LargestMovedPoint(pi) > n then
        return fail;
    fi;

    # we need the cycles of pi of length > 1 to be written such
    # that the minimum point is the initial point of the cycle
    initpts := [ ];
    cycles := [ ];
    for c in Filtered( Cycles( pi, [ 1 .. n ] ), c -> Length(c) > 1 ) do
        i := Minimum( c );
        Add( initpts, i );
        if i = c[1] then
            Add( cycles, c );
        else
            newc := [ i ];
            for k in [ 2 .. Length(c) ] do
                Add( newc, newc[k-1]^pi );
            od;
            Add( cycles, newc );
        fi;
    od;

    # R will be a straight line program from tau_1, sigma_1
    # we update cycle product, tau_i+1, sigma_i+1
    # and then overwrite the updates into positions 1,2,3
    R := [ [1,0], [3,1], [1,1], [2,1],
                  [[4,1],1], [[5,1],2], [[6,1],3] ];
    i := 1;

    # we keep track of which transposition of pi we must compute next
    nexttrpn := 1;

    repeat
      if i in initpts then
        # ci is the cycle of pi beginning with i
        ci := cycles[ Position( initpts, i ) ];
        # cycslp is the SLP for ci from tau_i and sigma_i
        # we carry forward the cycle product computed so far
        cycslp := [ 1,1 ];
        for k in [ 2 .. Length(ci) ] do
            j := ci[k];  # so (i,j)=(ci[1],ci[k])
            if j < n-1 then
                # NB: if i < j < n-1 then (i,j)(n-1,n) = (n-1,n)(i,j)
                if j = i+1 then
                    if IsEvenInt( n-i ) then
                        Append( cycslp, [ 3,i+2-n, 2,2, 3,1, 2,1,
                                          3,-1, 2,2, 3,n-i-2 ] );
                    else
                        Append( cycslp, [ 3,i+2-n, 2,1, 3,1, 2,1,
                                          3,-1, 2,1, 3,n-i-2 ] );
                    fi;
                else
                    if IsEvenInt( n-i ) then
                        Append( cycslp, [ 3,i+2-j, 2,1, 3,j-n,
                                          2,2, 3,1, 2,1, 3,-1, 2,2,
                                          3,n-j, 2,2, 3,j-i-2 ] );
                    elif IsOddInt( n-i ) and IsEvenInt( j-i-2 ) then
                        Append( cycslp, [ 3,i+2-j, 2,1, 3,j-n,
                                          2,1, 3,1, 2,1, 3,-1, 2,1,
                                          3,n-j, 2,2, 3,j-i-2 ] );
                    else
                        Append( cycslp, [ 3,i+2-j, 2,2, 3,j-n,
                                          2,1, 3,1, 2,1, 3,-1, 2,1,
                                          3,n-j, 2,1, 3,j-i-2 ] );
                    fi;
                fi;
            elif ( j = n-1 or j = n ) and i < n-1 then
                if ( j = n-1 and IsOddInt( nexttrpn ) ) or
                   ( j = n and IsEvenInt( nexttrpn ) ) then
                    if IsEvenInt( n-i ) then
                        if n-i>2 then
                           Append( cycslp,
                                [ 3,i+2-n, 2,2, 3,1, 2,1, 3,n-i-3  ] );
                        else
                           Append( cycslp, [ 2,2 ] );
                        fi;
                    else
                        Append( cycslp,
                                [ 3,i+2-n, 2,1, 3,1, 2,1, 3,n-i-3  ] );
                    fi;
                elif ( j = n and IsOddInt( nexttrpn ) ) or
                     ( j = n-1 and IsEvenInt( nexttrpn ) ) then
                    if IsEvenInt( n-i ) then
                        if n-i>2 then
                           Append( cycslp,
                                [ 3,i+3-n, 2,2, 3,-1, 2,1, 3,n-i-2  ] );
                        else
                           Append( cycslp, [ 2,1 ] );
                        fi;
                    else
                        Append( cycslp,
                                [ 3,i+3-n, 2,2, 3,-1, 2,2, 3,n-i-2  ] );
                    fi;
                fi;
            else   # (i,j) = (n-1,n)
                Append( cycslp, [ ] );
            fi;

            nexttrpn := nexttrpn + 1;
        od;
        Append( R, [ [cycslp,4] ] );

      else  # not (i in initpts)
        # we carry forward cycle product computed so far
        Append( R, [ [[1,1],4] ] );
      fi;

      # we update tau_i+1 and sigma_i+1
      if IsEvenInt(n-i) then
          nexttau   := [ 2,-1,3,-1,2,1,3,1,2,1 ];
          nextsigma := [ 3,1,5,1 ];
      else
          nexttau   := [ 2,-1,3,-1,2,2,3,1,2,1 ];
          nextsigma := [ 3,1,2,2,5,-1 ];
      fi;

      Append( R, [ [nexttau,5], [nextsigma,6],
                     [[4,1],1], [[5,1],2], [[6,1],3] ]);
      i := i + 1;

    until i > Maximum( initpts );

    # the return value
    Add(R,[ [1,1],1 ]);

    # R is a straight line program with 2 inputs
    R:=StraightLineProgramNC( R, 2 );

    return R;

end;

# TODO: Document this magic constant properly.
# (It is apparently the default for eps in FindHomMethodsPerm.)
RECOG.GiantEpsilon := 1/1024;

#! @BeginChunk Giant
#! The method tries to determine whether the input group <A>G</A> is
#! a giant (that is, <M>A_n</M> or <M>S_n</M> in its natural action on
#! <M>n</M> points). The output is either a data structure <M>D</M> containing
#! nice generators for <A>G</A> and a procedure to write an SLP for arbitrary
#! elements of <A>G</A> from the nice generators; or <K>NeverApplicable</K> if
#! <A>G</A> is not transitive; or <K>fail</K>, in the case that no
#! evidence was found that <A>G</A> is a giant, or evidence was found, but
#! the construction of <M>D</M> was unsuccessful.
#! If the method constructs <M>D</M> then the calling node becomes a leaf.
#! @EndChunk
BindRecogMethod("FindHomMethodsPerm", "Giant",
"tries to find Sn and An in their natural actions",
# TODO: expects input to be transitive, so should always be run after
# FindHomMethodsPerm.NonTransitive; model this better?
rec(validatesOrAlwaysValidInput := true),
function(ri)
    local grp,grpmem,mp,res,F,deg;
    grp := Grp(ri);
    if not IsPermGroup(grp) then
        return NeverApplicable;
    fi;
    if not IsTransitive(grp) then
        return NeverApplicable;
    fi;
    mp := MovedPoints(grp);
    # Decide whether group is a giant
    if RECOG.IsGiant(grp,mp) = fail then
        return TemporaryFailure;
    fi;
    grpmem := Group(ri!.gensHmem);
    grpmem!.pseudorandomfunc := [rec(
       func := function(ri) return RandomElm(ri,"Giant",true).el; end,
       args := [ri])];

    # Do constructive recognition for giants
    res := RECOG.RecogniseGiant(grpmem,RECOG.GiantEpsilon);
    if res = fail then
        return TemporaryFailure;
    fi;
    Setslptonice(ri, SLPOfElms(res.gens));
    # Note that when putting the generators into the record, we reverse
    # their order, such that it fits to the SLPforSn/SLPforAn function!
    Setslpforelement(ri,SLPforElementFuncsPerm.Giant);
    ri!.giantinfo := res;
    SetFilterObj(ri,IsLeaf);
    F := FreeGroup(2); # for presentation
    deg := Size(mp);
    # We set the presentations of Sn and An from
    # [CM80] "Generators and relations for discrete groups", (6.21), 6.3.
    # They coincide with the ones in
    # [BLN+03] "A black-box group algorithm for recognizing finite symmetric 
    # and alternating groups, I", (2.1), (2.2), (2.3),
    # except that one relation in (2.1) and one relation in (2.3) is incorrect.
    if res.stamp = "An" then
        SetSize(ri,Factorial(Length(mp))/2);
        SetIsRecogInfoForSimpleGroup(ri,true);
        rels := [ F.2^(deg-2), F.1^3 ];
        if deg mod 2 = 1 then
            Add(rels, (F.2*F.1)^deg);
            rels := Concatenation(
                rels,
                List([1..QuoInt(n-3, 2)], k -> (F.1*F.2^(-k)*F.1*F.2^k)^2)
            );
        else
            Add(rels, (F.2*F.1)^(deg-1));
            rels := Concatenation(
                rels,
                List([1..QuoInt(n-2, 2)], k -> (F.1^((-1)^k)*F.2^-k*F.1*F.2^k)^2)
            );
        fi;
    else
        SetSize(ri,Factorial(Length(mp)));
        SetIsRecogInfoForAlmostSimpleGroup(ri,true);
        # if deg>2 then
            # Relations on F.1=(1,2), F.2 = (1,...,deg) from [CM80, (6.21)]
            # TODO: Is this correct for d=1, 2?
            rels := [ F.1^2, F.2^deg, (F.1*F.2)^(deg-1), (F.1*(F.1^F.2))^3 ];
            rels := Concatenation(
                rels, List([2..QuoInt(deg, 2)], j -> (F.1*(F.1^(F.2^j)))^2)
            );
        # fi;
    fi;
    SetNiceGens(ri,StripMemory(res.gens));
    SetStdPresentation(ri,F / rels);
    return Success;
end);

SLPforElementFuncsPerm.Giant :=
  function(ri,g)
    local gg;
    gg := g^ri!.giantinfo.conjperm;
    # Note that when putting the generators into the record, we reverse
    # their order, such that it fits to the SLPforSn/SLPforAn function!
    if ri!.giantinfo.stamp = "An" then
        return RECOG.SLPforAn(ri!.giantinfo.degree,gg);
    else   # Sn
        return RECOG.SLPforSn(ri!.giantinfo.degree,gg);
    fi;
  end;
