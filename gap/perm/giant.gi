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
## returns a list cycList such that cycList[i] is a cycle of length lenList[i]
## for all 1 <= i <= Length(lenList).
## Each entry of lenList must be either a prime number or n.
## If no such list can be constructed in a random search with at most N tries
## or if lenList[i]>n for some i, then returns fail.
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
                    if k = n then
                        # The existence of a full cycle in rand guarantees that
                        # rand is equal to this full cycle.
                        cycList[i] := rand;
                    else
                        # orders is a the list of all l>=2 such that rand contains a l-cycle and
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
#F  ConjEltSn(<n>,<g>,<h>) . . . element c s.t. g^c=(1..n), h^c=(1,2)
##
##

RECOG.ConjEltSn :=  function( mp, g, h )

    local c,i,la,n,oo,pos,supp;

    n := Length(mp);
    la := mp[n];   # this is the largest moved point

    supp := MovedPoints( h );

    if supp[1]^g = supp[2] then pos := supp[1];
    else pos := supp[2];
    fi;

    c := [];
    for i in [ 1 .. n ] do
        c[pos] := i;
        pos := pos^g;
    od;
    oo := Difference([1..la],mp);
    for i in [1..Length(oo)] do
        c[oo[i]] := i+n;
    od;

    return PermList( c );

end;


######################################################################
##
#F  RecogniseSn(<n>, <grp>, <N>) . . . . . . recognition function
##
##

RECOG.RecogniseSn :=  function( mp, grp, eps )

    local le, N, gens, c, n;

    n := Length(mp);

    le := 0;
    while 2^le < eps^-1 do
        le := le + 1;
    od;

    # TODO: Document these magic constants. They are probably from some paper.
    # Also, Max Horn suggested that it may be better to use a smaller N.
    N := Int(24 * (4/3)^3 * le * 6 * n);

    gens := RECOG.NiceGeneratorsSn( grp, N );
    if gens = fail then
        Info(InfoGiants,1,"couldn't find nice generators for Sn");
        return fail;
    fi;

    c := RECOG.ConjEltSn( mp, gens[1], gens[2] );

    return rec( stamp := "Sn", degree := n,
                gens := Reversed(gens),  conjperm := c );

end;


########################################################################
##
#F  NiceGeneratorsAnEven(<n>,<grp>,<N>) . . find (2,n-2)-cycle, 3-cycle
##
##

RECOG.NiceGeneratorsAnEven := function ( grp, N )

    local mp, l, t, cyclen, a, b, c, i, fp, suppb, others, g, h, n;

    mp := MovedPoints(grp);
    n := Length(mp);
    l := One(grp);

    while N > 0 do
        N := N - 1;
        t := PseudoRandom( grp );
        # was: cyclen := Collected( CycleLengths( t, [1..n] ) );
        cyclen := CycleStructurePerm(t);

        # was: if IsBound(a) = false and [n-1,1] in cyclen then
        if IsBound(a) = false and IsBound(cyclen[n-2]) then
            # we found an $n-1$-cycle
            a := t;
        fi;

        if IsBound(b) = false and IsBound(cyclen[2]) and cyclen[2] = 1 and
               # Filtered( cyclen, x -> x[1] mod 3 = 0 ) = [ [ 3,1 ] ]
               ForAll( [2..QuoInt(n,3)], x->not IsBound(cyclen[3*x-1]) )
        then
            # we can get a $3$-cycle
            #b := t^(Lcm(List(cyclen,x->x[1]))/3);
            b := t^(Lcm(Filtered([2..n],x->IsBound(cyclen[x-1])))/3);
        fi;

        if IsBound(a) and IsBound(b) then
            i := 10*n;
            fp := Difference( mp, MovedPoints(a) )[1];
            suppb:= MovedPoints( b );
            while i > 0 do
                i := i-1;
                t := PseudoRandom( grp );
                if fp in List( suppb, x -> x^t ) then
                    c := b^t;
                    others := [ fp^c, (fp^c)^c ];
                    if others[1]^a = others[2] then
                        h := c;
                    elif others[2]^a = others[1] then
                        h := c^2;
                    else
                        h := Comm(c^a,c);   # h = (1,i,i+1)
                    fi;
                    g := a * h;
                    return [ g, h ];
                fi;
            od; # while

            return fail;
        fi;

    od; # loop over random elements

    return fail;

end;

#########################################################################
##
#F  NiceGeneratorsAnOdd(<n>,<grp>,<N>) . . . . find (n-2)-cycle, 3-cycle
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
## Thus if grp is the full alternating group on an odd number of points, then the
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
#F  ConjEltAnEven(<n>,<g>,<h>) . . . c s.t. g^c=(1,2)(3..n), h^c=(1,2,3)
##
##

RECOG.ConjEltAnEven := function( mp, g, h )
    local c,i,la,n,oo,pos,s1,s1g,supp;

    n := Length(mp);
    la := mp[n];    # this is the largest moved point

    supp := MovedPoints(h);  # {i,j,k} where h=(i,j,k), i^g=j, j^g=i
    s1 := supp[1];
    s1g := s1^g;

    c := [];
    if s1g in supp then      # {s1,s1g} = {i,j}
        if s1^h = s1g then   # [s1,s1g] = [i,j]
            c[s1] := 1;
            c[s1g] := 2;
        else
            c[s1g] := 1;
            c[s1] := 2;
        fi;
        pos := Difference(supp,Set([s1,s1g]))[1];
        for i in [3..n] do
            c[pos] := i;
            pos := pos^g;
        od;
        oo := Difference([1..la],mp);
        for i in [1..Length(oo)] do
            c[oo[i]] := i+n;
        od;

    else   # s1 = k
        if supp[2]^h = supp[2]^g then
            c[supp[2]] := 1;
            c[supp[3]] := 2;
        else
            c[supp[3]] := 1;
            c[supp[2]] := 2;
        fi;
        pos := s1;
        for i in [3..n] do
            c[pos] := i;
            pos := pos^g;
        od;
        oo := Difference([1..la],mp);
        for i in [1..Length(oo)] do
            c[oo[i]] := i+n;
        od;
    fi;

    return PermList( c );

end;


######################################################################
##
#F  ConjEltAnOdd(<n>,<g>,<h>) . . . . c s.t. g^c=(3..n), h^c=(1,2,3)
##
##

RECOG.ConjEltAnOdd := function( mp, g, h )
    local c,compt,i,la,n,oo,pos;

    n := Length(mp);
    la := mp[n];   # this is the largest moved point

    compt := Intersection( MovedPoints( g ), MovedPoints( h ) )[1];
    # compt is the common point moved by both g and h : so becomes 3

    c := [];
    c[ compt^h ] := 1;
    c[ (compt^h)^h ] := 2;

    pos := compt;

    for i in [3..n] do
        c[pos] := i;
        pos := pos^g;
    od;

    oo := Difference([1..la],mp);
    for i in [1..Length(oo)] do
        c[oo[i]] := i+n;
    od;

    return PermList(c);

end;


######################################################################
##
#F  RecogniseAn(<n>, <grp>, <N>) . . . . . . recognition function
##
##

RECOG.RecogniseAn :=  function( mp, grp, eps )

        local le, N, gens, c, n;

        n := Length(mp);

        le := 0;
        while 2^le < eps^-1 do
            le := le + 1;
        od;

        N := Int(24 * (4/3)^3 * le * 6 * n);

        if n mod 2 = 0 then
            gens := RECOG.NiceGeneratorsAnEven( grp, N );
        else
            gens := RECOG.NiceGeneratorsAnOdd( grp, N );
        fi;

        if gens = fail then
            Info(InfoGiants,1,"couldn't find nice generators for An");
            return fail;
        fi;

        if n mod 2 = 0 then
            c := RECOG.ConjEltAnEven( mp, gens[1], gens[2] );
        else
            c := RECOG.ConjEltAnOdd( mp, gens[1], gens[2] );
        fi;

        return rec( stamp := "An", degree := n,
                    gens := Reversed(gens), conjperm := c );
end;


######################################################################
##
#F  RecogniseGiant(<n>, <grp>, <N>) . . . . . . recognition function
##
##
##  This is the main function.
##  TODO: Document the precise meaning of the threshold eps. Does it come from a specific paper?
##

RECOG.RecogniseGiant :=  function( mp, grp, eps )

    if ForAny(GeneratorsOfGroup( grp ), x -> SignPerm(x) = -1) then
        return RECOG.RecogniseSn( mp, grp, eps );
    else
        return RECOG.RecogniseAn( mp, grp, eps );
    fi;

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
            Append( cycslp, [ 2,1, 3,ci[Length(ci)]-ci[1]-1 ] );
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
BindRecogMethod(FindHomMethodsPerm, "Giant",
"tries to find Sn and An in their natural actions",
# TODO: expects input to be transitive, so should always be run after
# FindHomMethodsPerm.NonTransitive; model this better?
rec(validatesOrAlwaysValidInput := true),
function(ri, grp)
    local grpmem,mp,res;
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
    res := RECOG.RecogniseGiant(mp,grpmem,RECOG.GiantEpsilon);
    if res = fail then
        return TemporaryFailure;
    fi;
    Setslptonice(ri, SLPOfElms(res.gens));
    # Note that when putting the generators into the record, we reverse
    # their order, such that it fits to the SLPforSn/SLPforAn function!
    Setslpforelement(ri,SLPforElementFuncsPerm.Giant);
    ri!.giantinfo := res;
    SetFilterObj(ri,IsLeaf);
    if res.stamp = "An" then
        SetSize(ri,Factorial(Length(mp))/2);
        SetIsRecogInfoForSimpleGroup(ri,true);
    else
        SetSize(ri,Factorial(Length(mp)));
        SetIsRecogInfoForAlmostSimpleGroup(ri,true);
    fi;
    SetNiceGens(ri,StripMemory(res.gens));
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
