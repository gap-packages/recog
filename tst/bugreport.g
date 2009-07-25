SLPforAn :=  function( n, pi )

    local cycles, initpts, c, newc,  R, i, nexttrpn, ci, cycslp, k, j,
          nexttau, nextsigma ;

    if IsOne(pi) then
        return StraightLineProgramNC( [[1,0]], 2 );
    fi;
    if SignPerm( pi ) = -1 then
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
                        Append( cycslp,
                                [ 3,i+2-n, 2,2, 3,1, 2,1, 3,n-i-3  ] );
                    else
                        Append( cycslp,
                                [ 3,i+2-n, 2,1, 3,1, 2,1, 3,n-i-3  ] );
                    fi;
                elif ( j = n and IsOddInt( nexttrpn ) ) or
                     ( j = n-1 and IsEvenInt( nexttrpn ) ) then
                    if IsEvenInt( n-i ) then
                        Append( cycslp,
                                [ 3,i+3-n, 2,2, 3,-1, 2,1, 3,n-i-2  ] );
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

g := AlternatingGroup(14);
repeat
   Print(".\c");
   x := PseudoRandom(g);
   s := SLPforAn(14,x);
   y := ResultOfStraightLineProgram(s,
                    [(1,2,3),(1,2)(3,4,5,6,7,8,9,10,11,12,13,14)]);
until x<>y;

Print("\n",x/y,"\n");
