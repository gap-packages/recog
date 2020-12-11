#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This files's authors include Frank Celler.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
##
##  The classical groups recognition.
##
#############################################################################
##
#F  PrimitivePrimeDivisors( <d>, <p> ) . . . . compute the ppds of  <p>^<d>-1
##
## ppds will be the product of all primitive prime divisors counting
## multiplicities of p^d-1 and noppds will be p^d-1/ppds.
##
##  cf. Neumann & Praeger, p 578/579 Procedure Psi(d,q) in
##  ``A Recognition Algorithm for special linear groups"
##  Proc. Lond. Math. Soc. (3) 65, 1992, pp 555-603.
##

PrimitivePrimeDivisors := function(d, q)

    local ddivs, c, a, ppds, noppds;

    if d < 1 or q < 2 then
        return fail;
    fi;
    if d = 1 then
        return rec( ppds := q-1, noppds := 1 );
    fi;

    noppds  := 1; ppds := q^d-1;

    # Throughout the loop ppds * noppds = q^d-1;
    # Eventually ppds will contain the ppds and noppds the others
    ddivs :=  PrimeDivisors(d);
    for c in ddivs do
        a := Gcd( ppds, q^(d/c)-1);
         # all primes in a are not ppds
        while a > 1 do
            noppds := a * noppds;
            ppds := ppds/a;
            a := Gcd(ppds, a);
        od;
    od;

    ## and return as ppds the product of all ppds and as
    ## noppds the quotient p^d-1/ppds
    return rec( ppds  := ppds, noppds := noppds );

end;





#############################################################################
##
#F  PPDIrreducibleFactor( <R>, <f>, <d>, <q> )  . . . .  large factors of <f>
##
##  Let <R> be a ring and <f> a polynomial of degree <d>.
##  This function returns false if <f> does not have an irreducible
##  factor of degree > d/2 and it returns the irreducible factor if it does.

PPDIrreducibleFactor := function ( R, f, d, q )
    local  px,  pow,  i,  cyc,  gcd,  a;

    # handle trivial case
    #if Degree(f) <= 2  then
    #    return false;
    #fi;

    # compute the deriviative
    a := Derivative( f );

    # if the derivative is nonzero then $f / Gcd(f,a)$ is squarefree
    if not IsZero(a)  then

        # compute the gcd of <f> and the derivative <a>
        f := Quotient( R, f, Gcd( R, f, a ) );
        # now f is square free

        # $deg(f) <= d/2$ implies that there is no large factor
        if Degree(f) <= d/2  then
            return false;
        fi;

        # remove small irreducible factors
        px  := X(LeftActingDomain(R));
        pow := PowerMod( px, q, f );
        for i  in [ 1 .. QuoInt(d,2) ]  do

            # next cyclotomic polynomial x^(q^i)-x
            # of course, already reduced mod f
            cyc := pow - px;

            # compute the gcd of <f> and <cyc>
            gcd := Gcd(f, cyc );
            if 0 < Degree(gcd)  then
                f := Quotient( f, gcd );
                # This removes all irreducible factors of degree i from f
                if Degree(f) <= d/2  then
                    return false;
                fi;
            fi;

            # replace <pow> by x^(q^(i+1))
            pow := PowerMod( pow, q, f );
        od;
        # Since all irreducible factors of degree <= d/2 are gone,
        # f must be irreducible itself at this stage.
        return StandardAssociate( R, f );

    # otherwise <f> is the <p>-th power of another polynomial <r>
    else
        return false;
    fi;

end;


# AllPpdsOfElement := function(F,m,p,a)
#     local R,RemovePrimes,c,char,cyc,d,der,div,e,ext,g,gcd,i,pm,pow,px,result;
#     RemovePrimes := function(n,toremove)
#       # This removes all primes occurring in toremove from n
#       local gcd;
#       while true do
#         gcd := Gcd(n,toremove);
#         if IsOne(gcd) then return n; fi;
#         n := n / gcd;
#       od;
#     end;
# 
#     d := Length(m);
#     if IsMatrix(m) then
#         c := CharacteristicPolynomial(F,F,m);
#     else
#         c := m;
#     fi;
#     char := Characteristic(F);
# 
#     # compute the deriviative to make it square free:
#     while true do
#         der := Derivative( c );
#         if not IsZero(der) then break; fi;
#         ext := ShallowCopy(ExtRepNumeratorRatFun(c));
#         for i in [1,3..Length(ext)-1] do
#             ext[i] := [ext[i][1],ext[i][2]/char];
#         od;
#         c := PolynomialByExtRep(FamilyObj(c),ext);
#     od;
#     # compute the gcd of <f> and the derivative <a>
#     R := PolynomialRing(F);
#     c := Quotient( R, c, Gcd( R, c, der ) );
#     # Now c is square free but still contains all irreducible factors
#     # that occurred in the characteristic polynomial
# 
#     # get hold of small irreducible factors
#     px  := Indeterminate(F);
#     pow := PowerMod( px, Size(F), c );
#     result := [];
#     for e  in [ 1 .. QuoInt(d,2) ]  do
# 
#         # next cyclotomic polynomial x^(q^e)-x
#         # of course, already reduced mod c
#         cyc := pow - px;
# 
#         # compute the gcd of <f> and <cyc>
#         gcd := Gcd(c, cyc );
#         #Print("deg c:",Degree(c)," deg gcd:",Degree(gcd)," e=",e,"\n");
#         if 0 < Degree(gcd)  then
#             c := Quotient( R, c, gcd );
#             # This removes all irreducible factors of degree e from c
#             # The product of those that divided c is gcd
#             for div in DivisorsInt(e) do
#               if not div in result then
#                 #Print("Doing ",div," as divisor of ",e,"\n");
#                 pm := PrimitivePrimeDivisors( div*a, p );
#                 ## pm contains two fields, noppds and ppds.
#                 ## ppds is the product of all ppds of p^(ae)-1
#                 ## and noppds is (p^(ae)-1)/ppds.
# 
#                 ## get rid of the non-ppd part
#                 ## g will be x^noppds in F[x]/<gcd>
#                 g := PowerMod( px, RemovePrimes(p^(a*e)-1,pm.ppds), gcd );
# 
#                 if not IsOne(g) then
#                     #Print("g=",g," adding ",div,"\n");
#                     AddSet(result,div);
#                 fi;
#               fi;
#             od;
#         fi;
# 
#         if IsOne(c) then break; fi;
# 
#         # replace <pow> by x^(q^(i+1))
#         pow := PowerMod( pow, Size(F), c );
#     od;
#     if not IsOne(c) then
#       for div in DivisorsInt(Degree(c)) do;
#         if not div in result then
#           # There might be one large degree factor, it is necessarily irred.:
#           pm := PrimitivePrimeDivisors( div*a, p );
#           g := PowerMod( px, RemovePrimes(p^(Degree(c)*a)-1,pm.ppds), c );
#           if not IsOne(g) then
#               AddSet(result,div);
#           fi;
#         fi;
#       od;
#     fi;
#     return result;
# end;
# 
# AllPpdsOfElement2 := function(F,m,p,a)
#     local RemovePrimes,c,char,d,div,e,f,facts,g,gcd,n,pm,px,result;
#     RemovePrimes := function(n,toremove)
#       # This removes all primes occurring in toremove from n
#       local gcd;
#       while true do
#         gcd := Gcd(n,toremove);
#         if IsOne(gcd) then return n; fi;
#         n := n / gcd;
#       od;
#     end;
# 
#     d := Length(m);
#     if IsMatrix(m) then
#         c := CharacteristicPolynomial(F,F,m);
#     else
#         c := m;
#     fi;
#     char := Characteristic(F);
#     facts := Unique(Factors(PolynomialRing(F),c));
#     px := Indeterminate(F);
# 
#     result := [];
#     for f  in facts do
#         e := Degree(f);
#         for div in DivisorsInt(e) do
#             if not div in result then
#                 pm := PrimitivePrimeDivisors( div*a, p );
#                 ## pm contains two fields, noppds and ppds.
#                 ## ppds is the product of all ppds of p^(ae)-1
#                 ## and noppds is (p^(ae)-1)/ppds.
# 
#                 ## get rid of the non-ppd part
#                 ## g will be x^noppds in F[x]/<gcd>
#                 g := PowerMod( px, RemovePrimes(p^(a*e)-1,pm.ppds), f );
#                 if not IsOne(g) then
#                     AddSet(result,div);
#                 fi;
#             fi;
#         od;
#     od;
#     return result;
# end;


#############################################################################
##
#F  IsPpdElement( <F>, <m>, <d>, <p>, <a> )
##
##  This function takes as input:
##
##  <F>  field
##  <m>  a matrix or a characteristic polynomial
##  <d>  degree of <m>
##  <p>  a prime power
##  <a>  an integer
##
##  It tests whether <m> has order divisible by a primitive prime divisor of
##  p^(e*a)-1 for some e with d/2 < e <= d and returns false if this is not
##  the case. If it is the case it returns a list with two entries,
##  the first being e and the second being a boolean islarge, where
##  islarge is true if the order of <m> is divisible by a large ppd of
##  p^(e*a)-1 and false otherwise.
##
##  Note that if q = p^a with p a prime then a call to
##  IsPpdElement( <F>, <m>, <d>, <q>, 1 ) will test whether m is a
##  ppd(d, q; e) element for some e > d/2 and a call to
##  IsPpdElement( <F>, <m>, <d>, <p>, <a> ) will test whether m is a
##  basic ppd(d, q; e) element for some e > d/2.
##
InstallGlobalFunction( IsPpdElement, function( F, m, d, p, a )
    local   c, e,  R,  pm,  g, islarge;

    # compute the characteristic polynomial
    if IsMatrix(m)  then
      c := CharacteristicPolynomial( m );
    else
      c := m;
    fi;

    # try to find a large factor
    R := PolynomialRing(F);
    c := PPDIrreducibleFactor( R, c, d, p^a );

    # return if we failed to find one
    if c = false  then
        return false;
    fi;

    e  := Degree(c);
    ## find the noppds and ppds parts
    pm := PrimitivePrimeDivisors( e*a, p );
    ## pm contains two fields, noppds and ppds.
    ## ppds is the product of all ppds of p^(ae)-1
    ## and noppds is p^(ae)-1/ppds.

    ## get rid of the non-ppd part
    ## g will be x^noppds in F[x]/<c>
    g := PowerMod( Indeterminate(F), pm.noppds, c );

    ## if g is one there is no ppd involved
    if IsOne(g) then
        return false;
    fi;

    ## now we know that <m> is a ppd-element

    ## bug fix 31.Aug.2007 ACN
    if pm.ppds mod (e+1) <> 0 then
        ## we know that all primes dividing pm.ppds are large
        ## and hence we know <m> is a large ppd-element
        islarge := true;
        return [e, islarge];
    fi;


    ## Now we know (e+1) divides pm.ppds and (e+1) has to be
    ## a prime since all ppds are at least (e+1)
    if not IsPrimeInt (e+1) then
         return false;
    fi;

    g := PowerMod( g, e+1, c );
    ## so g := g^(e+1) in F[x]/<c>
    if IsOne(g)  then
        ## (e+1) is the only ppd dividing |<m>| and only once
        islarge := false;
        return [ e, islarge ];
    else
        ## Either another ppd also divides |<m>| and this one is large or
        ## (e+1)^2 divides |<m>| and hence still large
        islarge := true;
        return [ e, islarge  ];
    fi;


end );


#############################################################################
##
#F  PPDIrreducibleFactorD2(  <f>, <d>, <q> )  . . . .  d/2-factors of <f>
##
PPDIrreducibleFactorD2 := function ( f, d, q )

    local i;

    if d mod 2 <> 0 then
        Print( "d must be divisible by 2\n" );
        return false;
    fi;

    f := Factors( f );

    for i in [ 1 .. Length(f) ] do
        if Degree( f[i] ) = d/2 then
            return f[i];
        fi;
    od;

    return false;

end;

#############################################################################
##
#F  IsPpdElementD2( <F>, <m>, <e>, <p>, <a> )
##
##  This function takes as input:
##
##  <F>  field
##  <m>  a matrix or a characteristic polynomial
##  <d>  degree of <m>
##  <p>  a prime power
##  <a>  an integer
##
##  It tests whether <m> has order divisible by a primitive prime divisor
##  of p^(e*a)-1 for e = d/2 and returns false if this is not
##  the case. If it is the case it returns a list with three entries,
##  the first being e=d/2; the second being a boolean islarge, where
##  islarge is true if the order of <m> is divisible by a large ppd of
##  p^(e*a)-1 and false otherwise; and the third is noppds (the first
##  return value of PrimitivePrimeDivisors).
##
##  Note that if q = p^a then a call to
##  IsPpdElement( <F>, <m>, <d>, <q>, 1 ) will test whether m is a
##  ppd(d, q; e) element for e = d/2 and a call to
##  IsPpdElement( <F>, <m>, <d>, <p>, <a> ) will test whether m is a
##   basic ppd(d, q; e) element for e = d/2.
##
InstallGlobalFunction( IsPpdElementD2, function( F, m, e, p, a )
    local   c,  R,  pm,  g, islarge;

    # compute the characteristic polynomial
    if IsMatrix(m)  then
        c := CharacteristicPolynomial( m );
    else
        c := m;
    fi;

    # try to find a large factor
    c := PPDIrreducibleFactorD2(  c, e, p^a );

    # return if we failed to find one
    if c = false  then
        return false;
    fi;

    ## find the nonppds and ppds parts
    pm := PrimitivePrimeDivisors( Degree(c)*a, p );
    ## pm contains two fields, noppds and ppds.
    ## ppds is the product of all ppds of p^(ad/2)-1
    ## and noppds is p^(ad/2)-1/ppds.


    # get rid of the non-ppd part
    g := PowerMod( Indeterminate(F), pm.noppds, c );

    # if it is one there is no ppd involved
    if IsOne(g)  then
        return false;
    fi;
    # now we know that g is a ppd-d/2-element

    # compute the possible gcd with <e>+1
    e   := Degree(c);
    if pm.ppds mod (e+1) <> 0 then
        # we know that all primes dividing pm.ppds are large
        # and hence we know g is a large ppd-element
        islarge := true;
        return [ e, islarge, pm.noppds ];
    fi;

    # Now we know (e+1) divides pm.ppds and (e+1) has to be
    # a prime since all ppds are at least (e+1)
    if not IsPrimeInt(e+1) then
        return false;
    fi;
    g := PowerMod( g, e+1, c );
    if IsOne(g)  then
        # (e+1) is the only ppd dividing |<m>| and only once
        islarge := false;
        return [ e, islarge, pm.noppds ];
    else
        # Either another ppd divides m and this one is large or
        # (e+1)^2 divides |<m>| and hence still large
        islarge := true;
        return [ Degree(c), islarge, pm.noppds ];
    fi;

end);
