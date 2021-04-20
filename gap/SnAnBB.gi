#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This files's authors include Maska Law, Alice C. Niemeyer, Ákos Seress.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
##
##  This file provides code for recognising whether a black box group
##  with known degree n is isomorphic to A_n or S_n.
##
##  The code is based upon the algorithm presented in the paper [BLGN+03].
##
##
RECOG.SatisfiesSnPresentation := function(ri, n, r, s)
    local j, t;
    if not isone(ri)((r * s)^(n-1)) then
        return false;
    fi;
    j := 2;
    t := r;
    while j <= n/2 do
        t := t * r;
        if not isone(ri)(Comm(s,t)^2) then
            return false;
        fi;
        j := j + 1;
    od;
    return true;
end;

RECOG.SatisfiesAnPresentation := function(ri, s, t, n)
    local j, r, ti, tr;

    if not isone(ri)(s^(n-2)) or not isone(ri)(t^3) then
        return false;
    fi;

    if IsOddInt(n) then
        # we already know s^(n-2) = t^3 = 1
        if not isone(ri)((s * t)^n) then
            return false;
        fi;
        tr := t;
        for j in [1..(n-3)/2] do
            tr := tr ^ s; # equal to t^(s^j)
            if not isone(ri)((t * tr)^2) then
                return false;
            fi;
        od;
        return true;
    else
        # we already know s^(n-2) = t^3 = 1
        if not isone(ri)((s * t)^(n-1)) then
            return false;
        fi;
        j := 1;
        r := s^0;
        ti := t^-1;
        while j <= (n-2)/2  do
            r := r * s;
            if (IsEvenInt(j) and not isone(ri)((t *(t^r))^2)) or
               (IsOddInt(j) and not isone(ri)((ti *(t^r))^2)) then
                return false;
            fi;
            j := j + 1;
        od;
        return true;
    fi;
end;

RECOG.Binary := function( i, m )
    local j, bin, le;
    bin := [];
    for j in [ 1 .. m ] do
        Add( bin, i mod 2 );
        i := QuoInt(i,2);
    od;
    for j in [m+1 .. 2 * m ] do
        bin[j] := 1 - bin[j-m];
    od;
    return bin;
end;

RECOG.ConstructXiSn := function( n, g, h )
    local a, c, xis, xisl, k, m, b, i, j, q, q2, q4, g2, g4, conj, pow;

    k := QuoInt( n, 3 );
    a := h^g * h; # a := (1,2,3);
    c := g^3;
    q := (g^(-1)*h);
    q2 := q^2;
    q4 := q2^2;
    conj := g^2;
    g2 := conj;
    g4 := g2^2;
    pow := g^(-1);

    # m = Ceil( log_2 (k+1) )
    m := 0;
    while 2^m < k+1 do
        m := m + 1;
    od;

    if (n mod 3) = 0 then
        xis  := List( [1..2*m+4], i -> h^0 );
        xisl := List( [1..2*m+4], i -> [ ] );
        for i in [ 1 .. k ] do
            if ((i mod 2) = 1) and (i < k) then
                xis[m+2] := xis[m+2]*a^(conj*pow);
                Add(xisl[m+2],[3*i-1..3*i+1]);
                xis[m+1] := xis[m+1]*a^((conj*pow)^2);
                Add(xisl[m+1],[3*i..3*i+2]);
                conj := conj * q;
                pow := pow * g;
                xis[2*m+4] := xis[2*m+4]*a^((conj*pow)^3);
                Add(xisl[2*m+4],[3*i-2,3*i+2,3*i+3]);
                conj := conj *q;
                pow := pow *g;
                xis[2*m+3] := xis[2*m+3]*a^((conj*pow)^3);
                Add(xisl[2*m+3],[3*i-2,3*i-1,3*i+3]);
                conj := conj * q4;
                pow := pow * g4;
            fi;
            b := RECOG.Binary(i, m);
            for j in [1 .. m] do
                if b[j] = 1 then
                    xis[j] := xis[j] * a;
                    Add(xisl[j],[3*i-2..3*i] );  # al;
                fi;
                if b[j+m] = 1 then
                    xis[j+m+2] := xis[j+m+2] * a;
                    Add(xisl[j+m+2],[3*i-2..3*i] );  # al;
                fi;
            od;
            a := a^c;
        od;
    else  # n mod 3 > 0
        xis  := List( [1..2*m+6], i -> h^0 );
        xisl := List( [1..2*m+6], i -> [ ] );
        for i in [ 1 .. k ] do
            if ((i mod 2) = 1) and (i < k) then
                xis[m+2] := xis[m+2]*a^(conj*pow);
                Add(xisl[m+2],[3*i-1..3*i+1]);
                xis[m+1] := xis[m+1]*a^((conj*pow)^2);
                Add(xisl[m+1],[3*i..3*i+2]);
                conj := conj * q;
                pow := pow * g;
                xis[2*m+5] := xis[2*m+5]*a^((conj*pow)^3);
                Add(xisl[2*m+5],[3*i-2,3*i+2,3*i+3]);
                conj := conj *q;
                pow := pow *g;
                xis[2*m+4] := xis[2*m+4]*a^((conj*pow)^3);
                Add(xisl[2*m+4],[3*i-2,3*i-1,3*i+3]);
                conj := conj * q4;
                pow := pow * g4;
            fi;
            b := RECOG.Binary(i, m);
            for j in [1 .. m] do
                if b[j] = 1 then
                    xis[j] := xis[j] * a;
                    Add(xisl[j],[3*i-2..3*i] );  # al;
                fi;
                if b[j+m] = 1 then
                    xis[j+m+3] := xis[j+m+3] * a;
                    Add(xisl[j+m+3],[3*i-2..3*i] );  # al;
                fi;
            od;
            a := a^c;
        od;
        if (n mod 3) =1 then
            xis[m+3] := a;
            xisl[m+3] := [[1,2,n]];
        elif (n mod 3) =2 then
            xis[m+3] := a;
            xisl[m+3] := [[1,n-1,n]];
        fi;
    fi;

    xisl:=List(xisl,z->Union(z));

    return [xis, xisl];

end;

##  Test whether i^z = j
RECOG.IsImagePointSn := function(ri, n, z, g,  h, j,  t1z, t2z)
    local s, k, cnt, gj;

    gj := g^(j-3);
    s := [];
    s[1] := (h^(h^g))^gj;
    s[2] := h^(gj*g);
    s[3] := s[2]^g;
    s[4] := s[1]^(g^2);

    cnt := 0;
    for k in [ 1 .. 4 ] do
        if not isequal(ri)(t1z*s[k],s[k]*t1z) then
            cnt := cnt + 1;
        fi;
    od;
    if cnt < 3 then return false; fi;

    cnt := 0;
    for k in [ 1 .. 4 ] do
        if not isequal(ri)(t2z*s[k],s[k]*t2z) then
            cnt := cnt + 1;
        fi;
    od;
    if cnt < 3 then return false; fi;

    return true;

end;

##  Determine the image of z under lambda
RECOG.FindImageSn := function(ri, n, z, g, h, xis, xisl)
    local i, j, l, t, tz, k, sup, m, rest, lp1, mxj, mxjpm, zim, OrderSup;

    m := Length(xisl)/2;
    t := [h,h^g];
    t[3] := h^(t[2]);
    k := g^3;
    zim := [];

    # compute images of i, i+1 and i+2
    i := 1;
    while i <= n-2 do
        tz := List( t, x->x^z );
        sup := [ [1..n], [1..n], [1..n] ];
        for j in [1 .. m] do  # loop over xis
            l := 1;
            mxj := xisl[j];
            mxjpm := xisl[j+m];
            while l <= 3 do  # limit support of i+l-1
                lp1 := l mod 3 + 1;
                if isequal(ri)(tz[l]*xis[j],xis[j]*tz[l]) then
                    sup[l] := Difference( sup[l], mxj);
                    sup[lp1] := Difference( sup[lp1], mxj);
                    if isequal(ri)(tz[lp1]*xis[j],xis[j]*tz[lp1]) then
                        sup[lp1 mod 3 + 1] :=
                            Difference( sup[lp1 mod 3 + 1], mxj);
                    else
                        sup[lp1 mod 3 + 1] :=
                            Difference( sup[lp1 mod 3 + 1], mxjpm);
                    fi;
                    l := 4;  # exit loop over l
                elif isequal(ri)(tz[l]*xis[j+m],xis[j+m]*tz[l]) then
                    sup[l] := Difference( sup[l], mxjpm);
                    sup[lp1] := Difference( sup[lp1], mxjpm);
                    if isequal(ri)(tz[lp1]*xis[j+m],xis[j+m]*tz[lp1]) then
                        sup[(lp1) mod 3 + 1] :=
                            Difference( sup[lp1 mod 3 + 1], mxjpm);
                    else
                        sup[lp1 mod 3 + 1] :=
                            Difference( sup[lp1 mod 3 + 1], mxj);
                    fi;
                    l := 4;  # exit loop over l
                fi;
                l := l + 1;
            od;
        od;

        # now the images of i,i+1,i+2 should be determined up to 5 points
        for l in [ 1 .. 3 ] do
            lp1 := l mod 3 + 1;
            for j in sup[l] do
                if not IsBound(zim[i+l-1]) then
                    if Length(sup[l]) = 1 then
                        zim[i+l-1] := sup[l][1];
                    elif RECOG.IsImagePointSn(ri,n,z,g,h,j,t[l]^z,t[lp1 mod 3+1]^z)
                        then zim[i+l-1] := j;
                    fi;
                fi;
            od;
        od;

        i := i + 3;
        t[1] := t[1]^k;
        t[2] := t[1]^g;
        t[3] := t[1]^t[2];

    od;  # while

    if RemInt(n,3) = 1 then
        zim[n] := Difference([1..n],zim)[1];
    fi;

    if RemInt(n,3) = 2 then
        sup := Difference([1..n],zim);
        if RECOG.IsImagePointSn(ri, n,z,g,h,sup[1],(h^(g^(-1)))^z,
                                                 (h^(g^(-2)))^z ) then
            zim[n] := sup[1];
        else
            zim[n] := sup[2];
        fi;
        zim[n-1] := Difference(sup,[zim[n]])[1];
    fi;

    if Length(Set(zim)) <> n then return fail; fi;

    return PermList(zim);
end;

RECOG.ConstructXiAn := function( n, g, h )
    local a, c, xis, xisl, k, m, b, i, j, cyc5, cyc, cyc10,
          a1, b1, a2, b2, aux, a3, b3, anew;

    k := QuoInt( n, 5 );
    # m = Ceil( log_2 (k+1) )
    m := 0;
    while 2^m < k+1 do
        m := m + 1;
    od;

    c := g^5;

    if (n mod 2) = 1 then
        if (n mod 5) = 0 then
            a := h * (h^g)^(-1) * h^(g^2); # (1,2,3,4,5)
            cyc := g*h; # (1,2,3,...,n)
            cyc5 := cyc^5;
            cyc10 := cyc5^2;
            a1 := a^(cyc^2); # (3,4,5,6,7)
            b1 := a^c;  # (1,2,8,9,10)
            anew := a^(cyc^5); # (6,7,8,9,10)
            a2 := (b1^h)^anew; # (2,3,9,10,6)
            b2 := (a1^h)^anew; # (1,4,5,7,8)
            aux := a1^(g^2); # (5,6,7,8,9)
            a3 := a1^(aux^2); # (3,4,7,8,9)
            b3 := ((a^aux)^(anew^2))^(g^2); # (1,2,5,6,10)

            xis := [a];
            xisl := [ [ [1 .. 5] ] ];

            for j in [ 2 .. m] do
                xis[j]  := g^0;
                xisl[j] := [ ];
            od;

            xis[m+1] := a1;
            xisl[m+1] := [ [3..7] ];
            xis[m+2] := a2;
            xisl[m+2] := [ [2,3,6,9,10] ];
            xis[m+3] := a3;
            xisl[m+3] := [ [3,4,7,8,9] ];
            xis[m+4] := g^0;
            xisl[m+4] := [];

            for j in [m+5 .. 2*m+3 ] do
                xis[j] := a;
                xisl[j] := [ [1 .. 5] ];
            od;

            xis[2*m+4] := b1;
            xisl[2*m+4] := [ [1,2,8,9,10] ];
            xis[2*m+5] := b2;
            xisl[2*m+5] := [ [1,4,5,7,8] ];
            xis[2*m+6] := b3;
            xisl[2*m+6] := [ [1,2,5,6,10] ];

            for i in [ 2 .. k ] do
              if ((i mod 2) = 1) and (i<k) then
                a1 := a1^cyc10;
                b1 := b1^cyc10;
                a2 := a2^cyc10;
                b2 := b2^cyc10;
                a3 := a3^cyc10;
                b3 := b3^cyc10;
                xis[m+1] := xis[m+1] * a1;
                Add(xisl[m+1], [5*i-2..5*i+2] );
                xis[m+2] := xis[m+2] * a2;
                Add(xisl[m+2], [5*i-3,5*i-2,5*i+1,5*i+4,5*i+5] );
                xis[m+3] := xis[m+3] * a3;
                Add(xisl[m+3], [5*i-2,5*i-1,5*i+2,5*i+3,5*i+4] );
                xis[2*m+4] := xis[2*m+4] * b1;
                Add(xisl[2*m+4], [5*i-4,5*i-3,5*i+3,5*i+4,5*i+5] );
                xis[2*m+5] := xis[2*m+5] * b2;
                Add(xisl[2*m+5], [5*i-4,5*i-1,5*i,5*i+2,5*i+3] );
                xis[2*m+6] := xis[2*m+6] * b3;
                Add(xisl[2*m+6], [5*i-4,5*i-3,5*i,5*i+1,5*i+5] );
              fi;
              b := RECOG.Binary(i, m);
              for j in [1 .. m] do
                if b[j] = 1 then
                    xis[j]  := xis[j] * anew;
                    Add(xisl[j], [5*i-4 .. 5*i]);
                fi;
                if b[j+m] = 1 then
                    xis[j+m+3]  := xis[j+m+3] * anew;
                    Add(xisl[j+m+3], [5*i-4 .. 5*i]);
                fi;
              od;
              anew  := anew^cyc5;
            od;

        else # n mod 5 <> 0
            a := h * (h^g)^(-1) * h^(g^2); # (1,2,3,4,5)
            cyc := g*h; # (1,2,3,...,n)
            cyc5 := cyc^5;
            cyc10 := cyc5^2;
            a1 := a^(cyc^2); # (3,4,5,6,7)
            b1 := a^c;  # (1,2,8,9,10)
            anew := a^(cyc^5); # (6,7,8,9,10)
            a2 := (b1^h)^anew; # (2,3,9,10,6)
            b2 := (a1^h)^anew; # (1,4,5,7,8)
            aux := a1^(g^2); # (5,6,7,8,9)
            a3 := a1^(aux^2); # (3,4,7,8,9)
            b3 := ((a^aux)^(anew^2))^(g^2); # (1,2,5,6,10)

            xis := [a];
            xisl := [ [ [1 .. 5] ] ];

            for j in [ 2 .. m] do
                xis[j]  := g^0;
                xisl[j] := [ ];
            od;

            xis[m+1] := a1;
            xisl[m+1] := [ [3..7] ];
            xis[m+2] := a2;
            xisl[m+2] := [ [2,3,6,9,10] ];
            xis[m+3] := a3;
            xisl[m+3] := [ [3,4,7,8,9] ];
            xis[m+5] := g^0;
            xisl[m+5] := [];

            for j in [m+6 .. 2*m+4 ] do
                xis[j] := a;
                xisl[j] := [ [1 .. 5] ];
            od;

            xis[2*m+5] := b1;
            xisl[2*m+5] := [ [1,2,8,9,10] ];
            xis[2*m+6] := b2;
            xisl[2*m+6] := [ [1,4,5,7,8] ];
            xis[2*m+7] := b3;
            xisl[2*m+7] := [ [1,2,5,6,10] ];

            for i in [ 2 .. k ] do
              if ((i mod 2) = 1) and (i<k) then
                a1 := a1^cyc10;
                b1 := b1^cyc10;
                a2 := a2^cyc10;
                b2 := b2^cyc10;
                a3 := a3^cyc10;
                b3 := b3^cyc10;
                xis[m+1] := xis[m+1] * a1;
                Add(xisl[m+1], [5*i-2..5*i+2] );
                xis[m+2] := xis[m+2] * a2;
                Add(xisl[m+2], [5*i-3,5*i-2,5*i+1,5*i+4,5*i+5] );
                xis[m+3] := xis[m+3] * a3;
                Add(xisl[m+3], [5*i-2,5*i-1,5*i+2,5*i+3,5*i+4] );
                xis[2*m+5] := xis[2*m+5] * b1;
                Add(xisl[2*m+5], [5*i-4,5*i-3,5*i+3,5*i+4,5*i+5] );
                xis[2*m+6] := xis[2*m+6] * b2;
                Add(xisl[2*m+6], [5*i-4,5*i-1,5*i,5*i+2,5*i+3] );
                xis[2*m+7] := xis[2*m+7] * b3;
                Add(xisl[2*m+7], [5*i-4,5*i-3,5*i,5*i+1,5*i+5] );
              fi;
              b := RECOG.Binary(i, m);
              for j in [1 .. m] do
                if b[j] = 1 then
                    xis[j]  := xis[j] * anew;
                    Add(xisl[j], [5*i-4 .. 5*i]);
                fi;
                if b[j+m] = 1 then
                    xis[j+m+4]  := xis[j+m+4] * anew;
                    Add(xisl[j+m+4], [5*i-4 .. 5*i]);
                fi;
              od;
              anew  := anew^cyc5;
            od;

            xis[m+4] := anew;
            xisl[m+4] := [Union([1..5-(n mod 5)],[n+1-(n mod 5)..n])];
            xis[2*m+8] := g^0;
            xisl[2*m+8] := [];

        fi;  # n mod 5

    else  # n mod 2 = 0
        a := h * (h^g) * h^(g^2); # (1,2,3,4,5)
        anew := h^(g^7)*a^c*a^(g^3); # (6,7,8,9,10);
        if (n mod 5) = 0 then
            cyc := g*h^2; # (2,3,...,n)
            cyc5 := cyc^5;
            cyc10 := cyc5^2;
            a1 := (a^(cyc^2))^(h^2); # (3,4,5,6,7)
            b1 := a^c;  # (2,1,8,9,10)
            a2 := (b1^h)^anew; # (3,2,9,10,6)
            b2 := (a1^h)^anew; # (1,4,5,7,8)
            aux := a1^(g^2); # (5,6,7,8,9)
            a3 := a1^(aux^2); # (3,4,7,8,9)
            b3 := ((a^aux)^(anew^2))^(g^2); # (1,2,5,6,10)

            xis := [a];
            xisl := [ [ [1 .. 5] ] ];

            for j in [ 2 .. m] do
                xis[j]  := g^0;
                xisl[j] := [];
            od;

            xis[m+1] := a1;
            xisl[m+1] := [ [3..7] ];
            xis[m+2] := a2;
            xisl[m+2] := [ [2,3,6,9,10] ];
            xis[m+3] := a3;
            xisl[m+3] := [ [3,4,7,8,9] ];
            xis[m+4] := g^0;
            xisl[m+4] := [];

            for j in [m+5 .. 2*m+3 ] do
                xis[j] := a;
                xisl[j] := [ [1 .. 5] ];
            od;

            xis[2*m+4] := b1;
            xisl[2*m+4] := [ [1,2,8,9,10] ];
            xis[2*m+5] := b2;
            xisl[2*m+5] := [ [1,4,5,7,8] ];
            xis[2*m+6] := b3;
            xisl[2*m+6] := [ [1,2,5,6,10] ];

            a1 := a1^cyc10;
            b1 := ((b1^(cyc^2))^(h^2))^(cyc^8);
            a2 := a2^cyc10;
            b2 := ((b2^(cyc^2))^(h^2))^(cyc^8);
            a3 := a3^cyc10;
            b3 := ((b3^(cyc^2))^(h^2))^(cyc^8);

            for i in [ 2 .. k ] do
              if ((i mod 2) = 1) and (i<k) then
                xis[m+1] := xis[m+1] * a1;
                Add(xisl[m+1], [5*i-2..5*i+2] );
                xis[m+2] := xis[m+2] * a2;
                Add(xisl[m+2], [5*i-3,5*i-2,5*i+1,5*i+4,5*i+5] );
                xis[m+3] := xis[m+3] * a3;
                Add(xisl[m+3], [5*i-2,5*i-1,5*i+2,5*i+3,5*i+4] );
                xis[2*m+4] := xis[2*m+4] * b1;
                Add(xisl[2*m+4], [5*i-4,5*i-3,5*i+3,5*i+4,5*i+5] );
                xis[2*m+5] := xis[2*m+5] * b2;
                Add(xisl[2*m+5], [5*i-4,5*i-1,5*i,5*i+2,5*i+3] );
                xis[2*m+6] := xis[2*m+6] * b3;
                Add(xisl[2*m+6], [5*i-4,5*i-3,5*i,5*i+1,5*i+5] );
                a1 := a1^cyc10;
                b1 := b1^cyc10;
                a2 := a2^cyc10;
                b2 := b2^cyc10;
                a3 := a3^cyc10;
                b3 := b3^cyc10;
              fi;
              b := RECOG.Binary(i, m);
              for j in [1 .. m] do
                if b[j] = 1 then
                    xis[j] := xis[j] * anew;
                    Add(xisl[j], [5*i-4 .. 5*i]);
                fi;
                if b[j+m] = 1 then
                    xis[j+m+3] := xis[j+m+3] * anew;
                    Add(xisl[j+m+3], [5*i-4 .. 5*i]);
                fi;
              od;
              anew  := anew^cyc5;
            od;

        else  # n mod 5 <> 0
            cyc := g*h^2; # (2,3,...,n)
            cyc5 := cyc^5;
            cyc10 := cyc5^2;
            a1 := (a^(cyc^2))^(h^2); # (3,4,5,6,7)
            b1 := a^c;  # (2,1,8,9,10)
            a2 := (b1^h)^anew; # (3,2,9,10,6)
            b2 := (a1^h)^anew; # (1,4,5,7,8)
            aux := a1^(g^2); # (5,6,7,8,9)
            a3 := a1^(aux^2); # (3,4,7,8,9)
            b3 := ((a^aux)^(anew^2))^(g^2); # (1,2,5,6,10)

            xis := [a];
            xisl := [ [ [1 .. 5] ] ];

            for j in [ 2 .. m] do
                xis[j]  := g^0;
                xisl[j] := [ ];
            od;

            xis[m+1] := a1;
            xisl[m+1] := [ [3..7] ];
            xis[m+2] := a2;
            xisl[m+2] := [ [2,3,6,9,10] ];
            xis[m+3] := a3;
            xisl[m+3] := [ [3,4,7,8,9] ];
            xis[m+5] := g^0;
            xisl[m+5] := [];

            for j in [m+6 .. 2*m+4 ] do
                xis[j] := a;
                xisl[j] := [ [1 .. 5] ];
            od;

            xis[2*m+5] := b1;
            xisl[2*m+5] := [ [1,2,8,9,10] ];
            xis[2*m+6] := b2;
            xisl[2*m+6] := [ [1,4,5,7,8] ];
            xis[2*m+7] := b3;
            xisl[2*m+7] := [ [1,2,5,6,10] ];

            a1 := a1^cyc10;
            b1 := ((b1^(cyc^2))^(h^2))^(cyc^8);
            a2 := a2^cyc10;
            b2 := ((b2^(cyc^2))^(h^2))^(cyc^8);
            a3 := a3^cyc10;
            b3 := ((b3^(cyc^2))^(h^2))^(cyc^8);

            for i in [ 2 .. k ] do
              if ((i mod 2) = 1) and (i<k) then
                xis[m+1] := xis[m+1] * a1;
                Add(xisl[m+1], [5*i-2..5*i+2] );
                xis[m+2] := xis[m+2] * a2;
                Add(xisl[m+2], [5*i-3,5*i-2,5*i+1,5*i+4,5*i+5] );
                xis[m+3] := xis[m+3] * a3;
                Add(xisl[m+3], [5*i-2,5*i-1,5*i+2,5*i+3,5*i+4] );
                xis[2*m+5] := xis[2*m+5] * b1;
                Add(xisl[2*m+5], [5*i-4,5*i-3,5*i+3,5*i+4,5*i+5] );
                xis[2*m+6] := xis[2*m+6] * b2;
                Add(xisl[2*m+6], [5*i-4,5*i-1,5*i,5*i+2,5*i+3] );
                xis[2*m+7] := xis[2*m+7] * b3;
                Add(xisl[2*m+7], [5*i-4,5*i-3,5*i,5*i+1,5*i+5] );
                a1 := a1^cyc10;
                b1 := b1^cyc10;
                a2 := a2^cyc10;
                b2 := b2^cyc10;
                a3 := a3^cyc10;
                b3 := b3^cyc10;
              fi;
              b := RECOG.Binary(i, m);
              for j in [1 .. m] do
                if b[j] = 1 then
                    xis[j] := xis[j] * anew;
                    Add(xisl[j], [5*i-4 .. 5*i]);
                fi;
                if b[j+m] = 1 then
                    xis[j+m+4] := xis[j+m+4] * anew;
                    Add(xisl[j+m+4], [5*i-4 .. 5*i]);
                fi;
              od;
              anew  := anew^cyc5;
            od;

            xis[m+4] := anew;
            xisl[m+4] := [Union([2..6-(n mod 5)],[n+1-(n mod 5)..n])];
            xis[2*m+8] := g^0;
            xisl[2*m+8] := [];

        fi;  # n mod 5

    fi;  # n mod 2

    xisl := List(xisl, z->Union(z));

    return [xis,xisl];
end;

# Test whether i^z = j
RECOG.IsImagePointAn := function(ri, n, z, g, h, j, s, a, b, t1z, t2z)
    local sc, k, cnt, bj;

    sc := ShallowCopy(s);

    if n mod 2 = 0 and j-1 = 1 then
        for k in [ 1 .. 5 ] do sc[k] := sc[k]^a; od;
    elif n mod 2 = 0  and j > 1 then
        bj := b^(j-2);
        for k in [ 1 .. 5 ] do sc[k] := sc[k]^bj; od;
    else
        bj := b^(j-1);
        for k in [ 1 .. 5 ] do sc[k] := sc[k]^bj; od;
    fi;

    cnt := 0;
    for k in [ 1 .. 5 ] do
        if not isequal(ri)(t1z*sc[k],sc[k]*t1z) then
            cnt := cnt + 1;
        fi;
    od;
    if cnt < 4 then return false; fi;

    cnt := 0;
    for k in [ 1 .. 5 ] do
        if not isequal(ri)(t2z*sc[k],sc[k]*t2z) then
            cnt := cnt + 1;
        fi;
    od;
    if cnt < 4 then return false; fi;
    return true;
end;

##  Determine the image of z under lambda
RECOG.FindImageAn := function(ri, n, z, g, h, xis, xisl)
    local i, j, jj, d, dd, t, k, ind, indices, sup, m, rest, lp1,
          findp, mxj, mxjpm, zim, l, inds, a, b, c, tim, tc, tdz, s;

    m := Length(xisl)/2;
    # list of pairs of 3-cycles intersecting in i is in ith entry
    findp := [[1,7], [1,8], [1,5], [2,5], [4,7] ];
    ## Find two 3-cycles which have the other two points in common
    ## with the d-th 3-cycle, e.g.
    ## if t[d] = (1,2,3) then we want (1,2,4) and (1,2,5)
    tc := [[2,4],[1,7],[1,4],[1,3],[3,6],[1,5],[2,5],[2,3],[1,2],[1,5]];
    rest := [ 5*QuoInt(n,5)+1 .. 5*QuoInt(n,5) + RemInt(n,5) ];

    # first we have to construct 10 elements such that
    # their supports are all 3-subsets of {i, .., i+4}
    if n mod 2 <> 0 then
        b := g * h;  # the n-cycle
        c := (h^(b^2))*h;  # (1,2,3,4,5)
        t := [];
        for i in [ 0 .. 4 ] do
            Add(t,h^(c^i));
            Add(t,(h^(c*h^(-1)))^(c^i));
        od;
        a := b^0;
        tim := [[1,2,3], [1,2,4], [2,3,4], [2,3,5], [3,4,5],
                [1,3,4], [1,4,5], [2,4,5], [1,2,5], [1,3,5] ];
    else
        b := g * h;  # the (n-1)-cycle without 2
        c :=  (h^2*((h^2)^(b^2)) * h^2);  # (1,2,3,4,5)
        t := [];
        for i in [ 0 .. 4 ] do
            Add(t,h^(c^i));
            Add(t,((h^g)^(-1))^(c^i));
        od;
        tim := [[1,2,3], [1,2,4], [2,3,4], [2,3,5], [3,4,5],
                [1,3,4], [1,4,5], [2,4,5], [1,2,5], [1,3,5] ];
        a := c * (t[6]^(g^3) * t[6]^(g^5) * t[6]^(g^7))^(h^2);
        # (1,2,3,4,5,6,7,8,9,10,11)
    fi;

    s := [];
    s[1] := h;
    s[2] := s[1]^(c^3);
    s[3] := s[2]^(g^2);
    s[4] := s[3]^(g^2);
    s[5] := s[4]^(g^2);
    zim := [];

    # compute images of i, ..,  i+4
    i := 1;
    while i <= n-4 do
        tdz := List(t, x->x^z);
        sup := [ [1..n], [1..n], [1..n], [1..n], [1..n] ];
        for j in [1 .. m] do
            d := 1;
            mxj := xisl[j];
            mxjpm := xisl[j+m];
            while d <= 10 do
                if isequal(ri)(tdz[d]*xis[j],xis[j]*tdz[d]) then
                    sup[tim[d][1]] := Difference( sup[tim[d][1]], mxj);
                    sup[tim[d][2]] := Difference( sup[tim[d][2]], mxj);
                    sup[tim[d][3]] := Difference( sup[tim[d][3]], mxj);
                    k := tc[d];
                    for jj in [ 1 .. 2 ] do
                        dd := Difference(tim[k[jj]], tim[d])[1];
                        if isequal(ri)(tdz[k[jj]]*xis[j],xis[j]*tdz[k[jj]]) then
                            sup[dd] :=  Difference( sup[dd], mxj);
                        else
                            sup[dd] :=  Difference( sup[dd], mxjpm);
                        fi;
                    od;
                    d := 11;
                elif isequal(ri)(tdz[d]*xis[j+m],xis[j+m]*tdz[d]) then
                    sup[tim[d][1]] := Difference(sup[tim[d][1]], mxjpm);
                    sup[tim[d][2]] := Difference(sup[tim[d][2]], mxjpm);
                    sup[tim[d][3]] := Difference(sup[tim[d][3]], mxjpm);
                    k := tc[d];
                    for jj in [ 1 .. 2 ] do
                        dd := Difference(tim[k[jj]], tim[d])[1];
                        if isequal(ri)(tdz[k[jj]]*xis[j+m],xis[j+m]*tdz[k[jj]]) then
                            sup[dd] :=  Difference( sup[dd], mxjpm);
                        else
                            sup[dd] :=  Difference( sup[dd], mxj);
                        fi;
                    od;
                    d := 11;
                fi;
                d := d + 1;
            od;
        od;

        # Now determine the images of these 5 points
        for l in [ 1 .. 5 ] do
            if Length(sup[l]) = 1
                then zim[i+l-1] := sup[l][1];
            else
                for j in [1..Length(sup[l])] do
                    if not IsBound(zim[i+l-1]) then
                        if RECOG.IsImagePointAn(ri,n,z,g,h,sup[l][j],s,a,b,
                              t[findp[l][1]]^z, t[findp[l][2]]^z ) then
                            zim[i+l-1] := sup[l][j];
                        fi;
                    fi;
                od;
            fi;
        od;

        if i = 1 and (n mod 2 = 0) then
            t := List( t, j -> j^(a^5));
        else
            t := List( t, j -> j^(b^5));
        fi;

        i := i + 5;
    od;

    if RemInt(n,5) = 1 then
        zim[n] := Difference([1..n],zim)[1];
    elif RemInt(n,5) > 1 then
        t := List( t, j -> j^(b^(-5+RemInt(n,5))));
        for k in [ 1 .. RemInt(n,5)-1 ] do
            sup := Difference([1..n],zim);
            for j in sup do
                if not IsBound(zim[n+1-k]) then
                    if RECOG.IsImagePointAn(ri,n,z,g,h,j,s,a,b,
                          t[findp[6-k][1]]^z, t[findp[6-k][2]]^z ) then
                        zim[n+1-k] := j;
                        sup := Difference(sup,[j]);
                    fi;
                fi;
            od;
        od;
        zim[n+1-RemInt(n,5)] := sup[1];
    fi;

    if Length(Set(zim)) <> n then return fail; fi;

    return PermList(zim);
end;


# ######################################################################
# ##
# #F  RecogniseSnAn(<n>, <grp>, <N>) . . . . . . recognition function
# ##
# ##  The main function.
#
# # FIXME: dead code? (it's callers are all dead)
# RecogniseSnAn :=  function( n, grp, eps )
#
#     local N, gens, le, g, h, slp, gl, b, eval, xis;
#
#     le := 0;
#     while 2^le < eps^-1 do
#         le := le + 1;
#     od;
#
#     #N := Int(24 * (4/3)^3 * le * 6 * n);
#     N := 20 * n;
#
#     gens := NiceGeneratorsSnAn( n, grp, N );
#     if gens = fail then return fail; fi;
#
#     if gens[3] = "Sn" then
#         xis := RECOG.ConstructXiSn( n, gens[1], gens[2] );
#         for g in GeneratorsOfGroup(grp) do
#             gl := RECOG.FindImageSn( n, g, gens[1], gens[2], xis[1], xis[2] );
#             if gl = fail then return fail; fi;
#             slp := RECOG.SLPforSn( n, gl );
#             eval := ResultOfStraightLineProgram(slp, [gens[2],gens[1]]);
#             if not isequal(ri)(eval,g) then return fail; fi;
#         od;
#         return [ "Sn", [gens[1],gens[2]], xis ];
#     else
#         xis := RECOG.ConstructXiAn( n, gens[1], gens[2] );
#         for g in GeneratorsOfGroup(grp) do
#             gl := RECOG.FindImageAn( n, g, gens[1], gens[2], xis[1], xis[2] );
#             if gl = fail then return fail; fi;
#             if SignPerm(gl) = -1 then
#                 # we found an odd permutation,
#                 # so the group cannot be An
#                 slp := RECOG.SLPforAn( n, (1,2)*gl );
#                 eval:=ResultOfStraightLineProgram(slp,[gens[2],gens[1]]);
#                 h :=  eval * g^-1;
#                 if n mod 2 <> 0 then
#                     b := gens[1] * gens[2];
#                 else
#                     b := h * gens[1] * gens[2];
#                 fi;
#                 if RECOG.SatisfiesSnPresentation( n, b, h ) then
#                     xis := RECOG.ConstructXiSn( n, b, h );
#                     for g in GeneratorsOfGroup(grp) do
#                         gl := RECOG.FindImageSn(n,g,b,h,xis[1],xis[2] );
#                         if gl = fail then return fail; fi;
#                         slp := RECOG.SLPforSn(n, gl);
#                         eval := ResultOfStraightLineProgram(slp,[h,b]);
#                         if not isequal(ri)(eval,g) then return fail; fi;
#                     od;
#                     return [ "Sn", [b,h] ,xis ];
#                 else
#                     return fail;
#                 fi;
#             else
#                 slp := RECOG.SLPforAn( n, gl );
#                 eval:=ResultOfStraightLineProgram(slp,[gens[2],gens[1]]);
#                 if not isequal(ri)(eval,g) then return fail; fi;
#             fi;
#         od;
#
#         return ["An", [gens[1],gens[2]], xis];
#     fi;
#
# end;
#
# NiceGeneratorsSnAn := function ( n, grp, N )
#
#     local AddStack, g1, g2, g3, g4, g, h, a, b, c, t, i, k, l,
#           delta, elfound, m, x, y;
#
#     # we put the elements that we look for on stacks
#     AddStack := function( stk, e )
#         if Length(stk) = 0 then
#             stk[1] := e;
#         elif Length(stk) = 1 then
#             stk[2] := e;
#         else
#             stk[1] := stk[2];
#             stk[2] := e;
#         fi;
#     end;
#
#     elfound := [false, false, false, false];
#
#     delta := 1 - (n mod 2);
#
#     l := One(grp);
#
#     m := n mod 6;
#     if m = 0 then k := 5;
#     elif m = 1 then k := 6;
#     elif m = 2 or m = 4 then k := 3;
#     elif m = 3 or m = 5 then k := 4;
#     fi;
#
#     g1 := [];   # $n$-cycles
#     g2 := [];   # transpositions
#     g3 := [];   # $n$ or $n-1$-cycles
#     g4 := [];   # 3-cycles
#
#     while N > 0 do
#         N := N - 1;
#         t := PseudoRandom(grp);
#
#         # use this random element to check the transpositions
#         for a in g2 do
#             x := a * a^t;
#             if not(isone(ri)(x)) and not(isone(ri)(x^2)) and
#                not(isone(ri)(x^3)) then
#                 # a is not a transposition
#                 Info( InfoRecSnAn, 2, "a is not a transposition");
#                 RemoveElmList(g2,Position(g2,a));
#                 if Length(g2) = 0 then elfound[2] := false; fi;
#             fi;
#         od;
#
#         # use this random element to check the 3-cycle
#         for a in g4 do
#             x := a * a^t;
#             if not(isone(ri)(x)) and not(isone(ri)(x^2)) and
#                not(isone(ri)(x^3)) and not(isone(ri)(x^5)) then
#                 # a is not a 3-cycle
#                 Info( InfoRecSnAn, 2, "a is not a 3-cycle");
#                 RemoveElmList(g4,Position(g4,a));
#                 if Length(g4) =  0 then elfound[4] := false; fi;
#             fi;
#         od;
#
#         if not(isone(ri)(t)) and isone(ri)(t^n) then
#             # we hope we found an n-cycle
#             AddStack(g1,t);
#             elfound[1] := true;
#             Info( InfoRecSnAn, 2, "found n-cycle");
#             if delta = 0 then
#                 elfound[3] := true;
#                 AddStack(g3,t);
#             fi;
#         fi;
#
#         b := t^(n-2-delta);
#         if not(isone(ri)(b)) and isone(ri)(b^2) then
#             # we hope we found a 2(n-2)-cycle
#             AddStack(g2,b);
#             elfound[2] := true;
#             Info( InfoRecSnAn, 2, "found transposition");
#         fi;
#
#         if delta = 1 and not(isone(ri)(t))  and isone(ri)(t^(n-1)) then
#             # we hope we found an n or (n-1)-cycle
#             AddStack(g3,t);
#             elfound[3] := true;
#             Info( InfoRecSnAn, 2, "found (n-1)-cycle");
#         fi;
#
#         b := t^(n-k);
#         if not(isone(ri)(b)) and isone(ri)(b^3) then
#             # we hope we found a 3(n-k)-element
#             AddStack(g4,b);
#             elfound[4] := true;
#             Info( InfoRecSnAn, 2, "found 3-cycle");
#         fi;
#
#         # if we have an n-cycle and a transposition, test for Sn
#         if elfound[1] and elfound[2] then
#             # hopefully $g2\lambda$ is a transposition
#             for a in g2 do  # choose a transposition
#                 i := n-1;
#                 while N>0 and i>0 do # take up to n-1 conjugates,
#                                      # check if they match some n-cycle
#                     i := i-1;
#                     h := a^PseudoRandom(grp);
#                     # use this opportunity again to check that
#                     # a really is a transposition
#                     x := a*h;
#                     if not(isone(ri)(x)) and not(isone(ri)(x^2)) and
#                        not(isone(ri)(x^3)) then
#                         # a is not a transposition
#                         Info(InfoRecSnAn,2,"a is not a transposition");
#                         RemoveElmList(g2,Position(g2,a));
#                         if Length(g2) = 0 then elfound[2] := false; fi;
#                         i := 0;
#                     else
#                         for b in g1 do
#                           y := Comm(h, h^b);
#                           if not(isone(ri)(y)) and
#                              not(isone(ri)(y^2)) and isone(ri)(y^3) then
#                             Info(InfoRecSnAn,1,"found good transposition");
#                             if RECOG.SatisfiesSnPresentation( n, b, h ) then
#                               Info( InfoRecSnAn, 1,
#                                 "Group satisfies presentation for Sn ",N);
#                               return [ b, h, "Sn" ];
#                             else
#                               RemoveElmList(g1,Position(g1,b));
#                               if Length(g1)=0 then elfound[1]:=false;fi;
#                             fi;
#                           fi;
#                         od;  #for
#                     fi;
#                 od;  # while
#             od;  # for a in g2
#         fi;
#
#         # if we have an n- or (n-1)-cycle and a 3-cycle, test for An
#         if elfound[3] and elfound[4] and n mod 2 <> 0 then
#             for a in g4 do  # choose a 3-cycle
#                 i := 1 + Int(n/3);
#                 while N > 0 and i > 0 do
#                     i := i-1;
#                     c := a^PseudoRandom(grp);
#                     # use this opportunity again to check that
#                     # a really is a 3-cycle
#                     x := a * c;
#                     if not(isone(ri)(x)) and not(isone(ri)(x^2)) and
#                        not(isone(ri)(x^3)) and not(isone(ri)(x^5)) then
#                         # a is not a 3-cycle
#                         Info( InfoRecSnAn, 2, "a is not a 3-cycle");
#                         RemoveElmList(g4,Position(g4,a));
#                         if Length(g4)=0 then elfound[4]:=false;fi;
#                         i := 0;
#                     else
#                         for b in g3 do  # choose an n- or (n-1)-cycle
#                           if not(isone(ri)(Comm(c,c^b)))  then
#                             # hope: supp (c) = {1,2,k}
#                             t := c*c^b;
#                             if isequal(ri)(t^2,t) then
#                                 # k = 3
#                                 x := c^(b^2);
#                                 y := c^x;
#                                 if isone(ri)(Comm(y, y^(b^2))) then
#                                     # y\lambda = (1,5,2)
#                                     h := c^2;
#                                 else
#                                     # y\lambda = (1,2,4)
#                                     h := c;
#                                 fi;
#                             elif isone(ri)(Comm(c, c^(b^2))) then
#                                 # 5 <= k <= n -2
#                                 x := c^b;
#                                 y := c^x;
#                                 if isone(ri)(Comm(y,y^b)) then
#                                     # y = (1,3,k) hence c = (1,2,k)
#                                     h := Comm(c^2, x);
#                                 else
#                                     h := Comm(c,x^2);
#                                 fi;
#                             else
#                                 # k= 4, n-1
#                                 x := c^b;
#                                 y := c^x;
#                                 if isone(ri)(Comm(y,y^b)) then
#                                     # y = (n-1, 1, 3), c = (1,2,n-1)
#                                     h := Comm(c^2,x);
#                                 elif isone(ri)(Comm(y,y^(b^2))) then
#                                     # y = (1,4,5) c = (1,4,2)
#                                     h := Comm(c,x^2);
#                                 elif isone(ri)((y*y^b)^2) then
#                                     # y = (1, n-1, n)  c = (1, n-1, 2)
#                                     h := Comm(c,x^2);
#                                 else
#                                     # y = (1,3,4)  c = ( 1,2,4)
#                                     h := Comm(c^2,x);
#                                 fi;
#                             fi;
#
#                             g := b * h^2;
#
#                             if RECOG.SatisfiesAnPresentation( n, g, h ) then
#                               Info( InfoRecSnAn, 1,
#                               "Group satisfies presentation for An ",N);
#                               return [ g, h, "An" ];
#                             else
#                               RemoveElmList(g3,Position(g3,b));
#                               if Length(g3)=0 then elfound[3]:=false;fi;
#                             fi;
#                           fi;
#                         od;  # for b in g3
#                     fi;
#                 od;  # while
#             od; # for a in g4
#         fi;
#
#         # if we have an n- or (n-1)-cycle and a 3-cycle, test for An
#         if elfound[3] and elfound[4] and n mod 2 = 0 then
#             for a in g4 do
#                 i := Int(2 * n/3);
#                 while N > 0 and i > 0 do
#                     i := i-1;
#                     c := a^PseudoRandom(grp);
#                     # use this opportunity again to check that
#                     # a really is a 3-cycle
#                     x := a * c;
#                     if not(isone(ri)(x)) and not(isone(ri)(x^2)) and
#                        not(isone(ri)(x^3)) and not(isone(ri)(x^5)) then
#                         # a is not a 3-cycle
#                         Info( InfoRecSnAn, 2, "a is not a 3-cycle");
#                         RemoveElmList(g4,Position(g4,a));
#                         if Length(g4)=0 then elfound[4]:=false;fi;
#                         i := 0;
#                     else
#                         for b in g3 do
#                           if not(isone(ri)(Comm(c,c^b))) and
#                              not(isone(ri)(Comm(c,c^(b^2)))) and
#                              not(isone(ri)(Comm(c,c^(b^4)))) then
#                             # hope: supp (c) = {1,i,j}
#                             h := Comm(c^b,c);
#                             # h = (1,i,i+1)
#                             g := b * h;
#                             if RECOG.SatisfiesAnPresentation( n, g, h ) then
#                               Info( InfoRecSnAn, 1,
#                               "Group satisfies presentation for An ", N);
#                               return [ g, h, "An" ];
#                             else
#                               RemoveElmList(g3,Position(g3,b));
#                               if Length(g3)=0 then elfound[3]:=false;fi;
#                             fi;
#                           fi;
#                         od;
#                     fi;
#                 od;  # while
#             od;  # for a in g4
#         fi;
#
#     od; # loop over random elements
#
#     return fail;
#
# end;
