#############################################################################
##
##  ppd.gi        
##                                recog package
##                                                           Frank Celler
##
##  Copyright 2005-2008 by the authors.
##  This file is free software, see license information at the end.
##
##  The classical groups recognition.
##
##  $Id: classical.gi,v 1.9 2006/10/06 14:03:25 gap Exp $
##
#############################################################################
##
#F  PPDPartPDM1( <d>, <p> ) . . . . . . . . compute the ppd part in <p>^<d>-1
##
## Phi will be the product of all primitive prime divisors counting 
## multiplicities of p^d-1 and Psi will be p^d-1/Phi.
##
PPDPartPDM1B := function( d, p )
    local   Phi,  q,  i,  a,  Psi,  y;

    # compute the (repeated) gcd with p^d-1
    Psi := 1;
    Phi := p^d - 1;
    q := 1;
    for i  in [ 1 .. d-1 ]  do
        q := q * p; # q = p^i
        if d mod i = 0  then
            repeat
                a := GcdInt( Phi, q-1 );
                Phi := Phi / a;
                Psi := Psi * a;
            until a = 1;
        fi;
    od;

    ## and return as ppds the product of all ppds and as
    ## noppds the quotient p^d-1/ppds
    return rec( noppds := Psi, ppds := Phi );
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

        # $deg(f) <= d/2$ implies that there is no large factor
        if Degree(f) <= d/2  then
            return false;
        fi;

        # remove small irreducible factors
        px  := X(LeftActingDomain(R));
        pow := PowerMod( px, q, f );
        for i  in [ 1 .. QuoInt(d,2) ]  do

            # next cyclotomic polynomial x^(q^i)-x
            cyc := pow - px;

            # compute the gcd of <f> and <cyc>
            gcd := Gcd(f, cyc );
            if 0 < Degree(gcd)  then
                f := Quotient( f, gcd );
                if Degree(f) <= d/2  then
                    return false;
                fi;
            fi;

            # replace <pow> by x^(q^(i+1))
            pow := PowerMod( pow, q, f );
        od;
        return StandardAssociate( R, f );

    # otherwise <f> is the <p>-th power of another polynomial <r>
    else
        return false;
    fi;

end;


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
    pm := PPDPartPDM1B( e*a, p );
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
##  return value of PPDPartPDM1B).
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
    pm := PPDPartPDM1B( Degree(c)*a, p );
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

##
##  This program is free software: you can redistribute it and/or modify
##  it under the terms of the GNU General Public License as published by
##  the Free Software Foundation, either version 3 of the License, or
##  (at your option) any later version.
##
##  This program is distributed in the hope that it will be useful,
##  but WITHOUT ANY WARRANTY; without even the implied warranty of
##  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
##  GNU General Public License for more details.
##
##  You should have received a copy of the GNU General Public License
##  along with this program.  If not, see <http://www.gnu.org/licenses/>.
##
