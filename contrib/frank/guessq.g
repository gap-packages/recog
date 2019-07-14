

LeastRank := function(o, q)
  local p, ps, cycs, good;
  p := Factors(q)[1];
  while o mod p = 0 do
    o := o/p;
  od;
  ps := Set(Factors(o));
  cycs := List(ps, r-> OrderMod(q, r));
  # a p can also divide higher cyclotomic numbers of q, if it divides
  # the exponent as largest prime; need to throw these out
  # [Roitman: On Zsigmondy primes, Prop.2]
  good := Filtered([1..Length(ps)], i-> ForAll(cycs, n->
              n mod ps[i] <> 0 or Maximum(Factors(n)) <> ps[i]));
  return Sum(List(Set(cycs{good}),Phi));
end;


# q as indeterminate
q := X(Cyclotomics, "q");

#############################################################################
##
#F  GFOrderSimp( <ser>, <dim>, <ord>, <q> ) . . . . . . orders of simple groups
#F  of Lie type
##
##  This function returns the entries from the list in [Carter, p.75].
##  <ser> is the series, <dim> the dimension and <ord> the order of
##  the automorphism of the Dynkin diagram, <q> can be an indeterminate.
##  Example:  GFOrderSimp("A",3,2,q); returns the order of $SU_4(q)$.
##
GFOrderSimp:=function(ser, rk, F0ord, q)
  local s, erg, i;
  if Length(ser) > 1 and ser[1] in "23" then
    F0ord := INT_CHAR(ser[1])-48;
    ser := ser{[2..Length(ser)]};
  fi;
  if ser="A" or ser="~A" then
    s := (-1)^(F0ord-1);
    erg:=q^(rk*(rk+1)/2);
    for i in [2..rk+1] do
      erg:=erg*(q^i-s^i);
    od;
    return erg;
  elif (ser="B" or ser="C") and rk =2 and F0ord=2 then
    return q^4*(q^2-1)*(q^4+1);
  elif ser="B" or ser="C" then
    erg:=q^(rk^2);
    for i in [1..rk] do
      erg:=erg*(q^(2*i)-1);
    od;
    return erg;
  elif ser="D" and rk=4 and F0ord=3 then
    return q^12*(q^8+q^4+1)*(q^6-1)*(q^2-1);
  elif ser="D" then
    erg:=q^(rk*(rk-1));
    for i in [1..rk-1] do
      erg:=erg*(q^(2*i)-1);
    od;
    if F0ord=1 then
      return erg*(q^rk-1);
    elif F0ord=2 then
      return erg*(q^rk+1);
    fi;
  elif ser="G" and rk =2 and F0ord=2 then
    return q^6*(q^2-1)*(q^6+1);
  elif ser="G" and rk=2 then
    return q^6*(q^2-1)*(q^6-1);
  elif ser="F" and rk=4 and F0ord=2 then
    return q^24*(q^2-1)*(q^6+1)*(q^8-1)*(q^12+1);
  elif ser="F" and rk=4 and F0ord=1 then
    return q^24*(q^2-1)*(q^6-1)*(q^8-1)*(q^12-1);
  elif ser="E" and rk=6 and F0ord=2 then
    return q^36*(q^2-1)*(q^5+1)*(q^6-1)*(q^8-1)*(q^9+1)*(q^12-1);
  elif ser="E" and rk=6 and F0ord=1 then
    return q^36*(q^2-1)*(q^5-1)*(q^6-1)*(q^8-1)*(q^9-1)*(q^12-1);
  elif ser="E" and rk=7 then
    return q^63*(q^2-1)*(q^6-1)*(q^8-1)*(q^10-1)
                                     *(q^12-1)*(q^14-1)*(q^18-1);
  elif ser="E" and rk=8 then
    return q^120*(q^2-1)*(q^8-1)*(q^12-1)*(q^14-1)
                            *(q^18-1)*(q^20-1)*(q^24-1)*(q^30-1);
  else
    return fail;
  fi;
end;

MinimalDimBoundCrossCharSimp := function(ser, rk, F0ord, q)
  local res, n;
  if Length(ser) > 1 and ser[1] in "23" then
    F0ord := INT_CHAR(ser[1])-48;
    ser := ser{[2..Length(ser)]};
  fi;
  if ser in ["A", "~A"] and rk = 1 then
    if IsInt(q) then
      res := (q-1)/GcdInt(q-1,2);
      if q in [4,9] then
        res := res-1;
      fi;
    else
      # for all q
      res := (q-1)/2-1;
    fi;
  elif ser in ["A", "~A"] and F0ord = 1 then
    n := rk+1;
    if n = 3 and q in [2,4] then
      res := q;
    elif n = 4 and q in [2,3] then
      res := 19*q-31;
    elif IsInt(q) then
      res := (q^n-1)/(q-1)-n;
    else
      res := (q^n-1)/(q-1)-n-14;
    fi;
  elif ser = "C" and rk > 1 then
    if IsInt(q) and q mod 2 = 0 then
      res := (q^rk-1)*(q^rk-q)/2/(q+1);
    else
      # this is the smaller one for all q > 2 (group not simple for q=2)
      res := (q^rk-1)/2;
    fi;
  elif ser in ["A", "~A"] and F0ord = 2 and rk > 1 then
    n := rk+1;
    if n = 4 and q in [2,3] then
      res := 2*q;
    elif n mod 2 = 1 then
      res := (q^n-q)/(q+1);
    elif IsInt(q) then
      res := (q^n-1)/(q+1);
    else
      # for all q
      res := (q^n-1)/(q+1)-14;
    fi;
  elif ser in ["D", "~D"] and F0ord = 1 and rk > 3 then
    if rk = 4 and q = 2 then
      res := 8;
    elif q in [2,3] then
      res := (q^rk-1)*(q^(rk-1)-1)/(q^2-1)+7*q-21;
    elif IsInt(q) then
      res := (q^rk-1)*(q^(rk-1)+q)/(q^2-1)-rk;
    elif rk = 4 then
      res := (q^rk-1)*(q^(rk-1)-1)/(q^2-1)-27;
    else
      res := (q^rk-1)*(q^(rk-1)-1)/(q^2-1)-7;
    fi;
  elif ser in ["D", "~D"] and F0ord = 2 and rk > 3 then
    res := (q^rk+1)*(q^(rk-1)-q)/(q^2-1) - rk + 2;
  elif ser = "B" and rk > 2 then
    if rk = 3 and q = 3 then
      res := 27;
    elif q = 3 then
      res := (q^rk-1)*(q^rk-q)/(q^2-1);
    elif IsInt(q) and q mod 2 = 0 then
      # same as ser="C"
      res := MinimalDimBoundCrossCharSimp("C",rk,1,q);
    elif IsInt(q) then
      res := (q^(2*rk)-1)/(q^2-1)-rk;
    else
      # for all q, not optimal
      res := (q^rk-1)*(q^rk-q)/q/(q+1)-rk-22;
    fi;
  elif ser = "E" and rk = 6 and F0ord in [1,2] then
    res := q^9*(q^2-1);
  elif ser = "E" and rk = 7 then
    res := q^15*(q^2-1);
  elif ser = "E" and rk = 8 then
    res := q^27*(q^2-1);
  elif ser = "F" and rk = 4 and F0ord = 1 then
    if q = 2 then
      res := 44;
    elif IsInt(q) and q mod 2 = 0 then
      res := q^7*(q^3-1)*(q-1)/2;
    elif IsInt(q) then
      res := q^6*(q^2-1);
    else
      # for all q
      res := q^6*(q^2-1)-148;
    fi;
  elif ser = "G" and rk = 2 and F0ord = 1 then
    if q in [3,4] then
      res := 20 - 2*q;
    elif IsInt(q) then
      res := q*(q^2-1);
    else
      # all q
      res := q*(q^2-1)-48;
    fi;
  elif ser in ["D","~D"] and rk = 4 and F0ord = 3 then
    res := q^3*(q^2-1);
  elif ser = "B" and rk = 2 and F0ord = 2 then
    # here argument q is assumed to be the actual q^2
    if q = 8 then
      res := 8;
    elif IsInt(q) then
      res := (q-1)*Sqrt(q/2);
    else
      # all q, not good
      res := (q-1)*q/2;
    fi;
  elif ser = "G" and rk = 2 and F0ord = 2 then
    # here argument q is assumed to be the actual q^2
    res := q*(q-1);
  elif ser = "F" and rk = 4 and F0ord = 2 then
    # here argument q is assumed to be the actual q^2
    if IsInt(q) then
      res := q^4*(q-1)*Sqrt(q/2);
    else
      # all q, not good
      res := q^4*(q-1)*q/2;
    fi;
  else
    res := fail;
  fi;
  return res;
end;


#############################################################################
##
#F  PossibleCrossCharTypes( <ords>, <bnd> ) . . . possible q and Lie type from
#F  element order(s) and degree bound
##
##  Let G(q) be a simple group of Lie type. <ords> is one element order or a
##  list of element orders from G(q) and <bnd> is an integer such that G(q)
##  has a representation in some non-defining characteristic of degree <= <bnd>.
##
##  This function returns a list of lists of form [q, type, rank], each
##  describing a possible type of G(q). If 'type' is in ["A", "2A", "B", "C",
##  "D", "2D"] only the triple with maximal possible 'rank' is included.
##
##  The result contains the actual type of G(q).
##
##  If the actual q is not too small, then a very small number (say, 1 to 3)
##  given element orders will already lead to a very small result list.
##  For small actual q a slightly larger number (say, 10) element orders
##  can be useful.
##
PossibleCrossCharTypes := function(ords, bnd)
  local d, sords, res, p, q, lrk, mrk, ll, f, l, a, szs;
  if IsInt(ords) then
    ords := [ords];
  fi;
  d := Lcm(ords);
  sords := Set(ords);

  # If instead of bound 'bnd' is result of previous call then we only
  # compute a refinement
  if IsList(bnd) then
    res := [];
    for a in bnd do
      lrk := Maximum(List(sords, o-> LeastRank(o, a[1])));
      if IsInt(a[3])  then
        if lrk <= a[3] and GFOrderSimp(a[2], a[3], 1, a[1]) mod d = 0 then
          Add(res, a);
        fi;
      else
        ll := a[3][Length(a[3])];
        if lrk <= ll then
          if GFOrderSimp(a[2], ll, 1, a[1]) mod d = 0 then
            Add(res, [a[1], a[2], [Maximum(lrk, a[3][1])..ll]]);
          fi;
        fi;
      fi;
    od;
    return res;
  fi;

  # And now the main case with given bound
  res := [];
  # loop over p's until p^2 > 2*bnd+2; we  handle A_1 for big p below
  # also Suzuki and Ree groups are handled later
  p := 2;

  repeat
    # loop over q=p^f until p^2 > 2*bnd+2
    q := p;
    repeat
      # least rank
      lrk := Maximum(List(sords, o-> LeastRank(o, q)));
      # type A
      mrk := Maximum(lrk-1,1);
      while MinimalDimBoundCrossCharSimp("A",mrk+1,1,q) <= bnd do
        mrk := mrk+1;
      od;
      if mrk >= lrk and GFOrderSimp("A", mrk, 1, q) mod d = 0 then
        Add(res, [q,"A",[Maximum(lrk,1)..mrk]]);
      fi;
      ll := Maximum(lrk, 2);
      # type 2A
      mrk := Maximum(ll-1,1);
      while MinimalDimBoundCrossCharSimp("A",mrk+1,2,q) <= bnd do
        mrk := mrk+1;
      od;
      if mrk >= ll and GFOrderSimp("A", mrk, 2, q) mod d = 0 then
        Add(res, [q,"2A",[ll..mrk]]);
      fi;
      # type C
      mrk := Maximum(ll-1,1);
      while MinimalDimBoundCrossCharSimp("C",mrk+1,1,q) <= bnd do
        mrk := mrk+1;
      od;
      if mrk >= ll and GFOrderSimp("C", mrk, 1, q) mod d = 0 then
        Add(res, [q,"C",[ll..mrk]]);
      fi;
      ll := Maximum(lrk, 3);
      # type B
      mrk := Maximum(ll-1,1);
      while MinimalDimBoundCrossCharSimp("B",mrk+1,1,q) <= bnd do
        mrk := mrk+1;
      od;
      if mrk >= ll and GFOrderSimp("B", mrk, 1, q) mod d = 0 then
        Add(res, [q,"B",[ll..mrk]]);
      fi;
      ll := Maximum(lrk, 4);
      # type D
      mrk := Maximum(ll-1,1);
      while MinimalDimBoundCrossCharSimp("D",mrk+1,1,q) <= bnd do
        mrk := mrk+1;
      od;
      if mrk >= ll and GFOrderSimp("D", mrk, 1, q) mod d = 0 then
        Add(res, [q,"D",[ll..mrk]]);
      fi;
      # type 2D
      mrk := Maximum(ll-1,1);
      while MinimalDimBoundCrossCharSimp("D",mrk+1,2,q) <= bnd do
        mrk := mrk+1;
      od;
      if mrk >= ll and GFOrderSimp("D", mrk, 2, q) mod d = 0 then
        Add(res, [q,"2D",[ll..mrk]]);
      fi;
      # type G2, F4, 3D4, E6, 2E6, E7, E8
      if lrk <= 2 and MinimalDimBoundCrossCharSimp("G",2,1,q) <= bnd and
         GFOrderSimp("G", 2, 1, q) mod d = 0 then
        Add(res, [q, "G", 2]);
      fi;
      if lrk <= 4 and MinimalDimBoundCrossCharSimp("F",4,1,q) <= bnd and
         GFOrderSimp("F", 4, 1, q) mod d = 0 then
        Add(res, [q, "F", 4]);
      fi;
      if lrk <= 4 and MinimalDimBoundCrossCharSimp("D",4,3,q) <= bnd and
         GFOrderSimp("D", 4, 3, q) mod d = 0 then
        Add(res, [q, "3D", 4]);
      fi;
      if lrk <= 6 and MinimalDimBoundCrossCharSimp("E",6,1,q) <= bnd and
         GFOrderSimp("E", 6, 1, q) mod d = 0 then
        Add(res, [q, "E", 6]);
      fi;
      if lrk <= 6 and MinimalDimBoundCrossCharSimp("E",6,2,q) <= bnd and
         GFOrderSimp("E", 6, 2, q) mod d = 0 then
        Add(res, [q, "2E", 6]);
      fi;
      if lrk <= 7 and MinimalDimBoundCrossCharSimp("E",7,1,q) <= bnd and
         GFOrderSimp("E", 7, 1, q) mod d = 0 then
        Add(res, [q, "E", 7]);
      fi;
      if lrk <= 8 and MinimalDimBoundCrossCharSimp("E",8,1,q) <= bnd and
         GFOrderSimp("E", 8, 1, q) mod d = 0 then
        Add(res, [q, "E", 8]);
      fi;
      q := q*p;
    until q^2 > 2*bnd+2;
    # now only A_1(q) may be missing
    while q <= Gcd(2,q-1)*(bnd+1) do
      if (q^2*(q^2-1)) mod d = 0 then
        Add(res, [q, "A", 1]);
      fi;
      q := q*p;
    od;
    p := NextPrimeInt(p);
    # for bigger p only A_1(p) remains, this is handled next
  until p^2 > 2*bnd+2;

  # case A_1(p) for p big: need primes p such that d| p^2(p-1)(p+1) in
  # range [sqrt(2 bnd + 2)..2 bnd + 2]:
  f := Set(Factors(d));
  l := Filtered(f, n-> n <= 2*bnd+2 and n^2 >= 2*bnd+2);
  for p in l do
    if p^2*(p^2-1) mod d = 0 then
      Add(res, [p, "A", 1]);
    fi;
  od;
  # now p-1 or p+1 must be multiple of largest prime divisor of d
  f := f[Length(f)];
  l := RootInt(2*bnd+2);
  l := l - (l mod f);
  while l < 2*bnd+4 do
    for p in [l-1, l+1] do
      if IsPrimeInt(p) and p^2*(p^2-1) mod d = 0 and ForAll(sords,
          o-> LeastRank(o, p) <= 1) then
        Add(res, [p, "A", 1]);
      fi;
    od;
    l := l+f;
  od;

  # Sz = 2B_2(q^2), degree in non-def. char. > (q^3)/2
  p := 2;
  f := 1;
  while p^(3*f)/4 < bnd^2 do
    q := p^f;
    if q^2*(q-1)*(q^2+1) mod d = 0 then
      Add(res, [q, "2B", 2]);
    fi;
    f := f+2;
  od;
  # ree = 2G_2(q^2), degree in non-def. char. > (q^4)/2
  p := 3;
  f := 1;
  while p^(2*f)/2 < bnd do
    q := p^f;
    if q^3*(q^2-1)*(q^2-q+1) mod d = 0 then
      Add(res, [q, "2G", 2]);
    fi;
    f := f+2;
  od;
  # Ree = 2F_4(q^2), degree in non-def. char. > (q^11)/2
  p := 2;
  f := 1;
  while p^(11*f)/4 < bnd^2 do
    q := p^f;
    if q^12*(q^2-q+1)*(q^4-q^2+1)*(q-1)^2*(q+1)^2*(q^2+1)^2 mod d = 0 then
      Add(res, [p^f, "2F", 4]);
    fi;
    f := f+2;
  od;

  # order by size of group (first group in list)
  szs := [];
  for a in res do
    if IsInt(a[3]) then
      Add(szs, GFOrderSimp(a[2],a[3],1,a[1]));
    else
      Add(szs, GFOrderSimp(a[2],a[3][1],1,a[1]));
    fi;
  od;
  SortParallel(szs, res);

  return res;
end;

PossibleqNoA1 := function(ords, bnd)
  local d, res, p, maxfl, f, l;
  if IsInt(ords) then
    d := ords;
  else
    d := Lcm(ords);
  fi;
  res := [];
  # below we consider q = p^f
  p := 2;
  repeat
    # type A_l(q), degree in non-def. char. > (q^l)/2-1
    maxfl := LogInt(2*bnd+2, p);
    for f in [1..maxfl] do
      if Value(GFOrderSimp("A", Int(maxfl/f)), p^f) mod d = 0 then
        Add(res, [p^f, "A", Int(maxfl/f)]);
      fi;
    od;
    # type 2A_l(q), l > 1, can use same estimate for degree
    for f in [1..Int(maxfl/2)] do
      if Value(GFOrderSimp("A", Int(maxfl/f), 2), p^f) mod d = 0 then
        Add(res, [p^f, "2A", Int(maxfl/f)]);
      fi;
    od;
    # type C_l(q), l > 1, can use same estimate for degree
    for f in [1..Int(maxfl/2)] do
      if Value(GFOrderSimp("C", Int(maxfl/f)), p^f) mod d = 0 then
        Add(res, [p^f, "C", Int(maxfl/f)]);
      fi;
    od;
    # type B_l(q), l > 2, degree in non-def. char. > q^(2l-2)/2
    maxfl := LogInt(2*bnd, p); # maximal 2 f (l-1)
    for f in [1..Int(maxfl/4)] do
      if Value(GFOrderSimp("B", Int(maxfl/f/2)+1), p^f) mod d = 0 then
        Add(res, [p^f, "B", Int(maxfl/f/2)+1]);
      fi;
    od;
    # type D_l(q) and 2D_l(q), l > 3, degree in non-def. char. > q^(2l-3)/2
    maxfl := LogInt(2*bnd, p); # maximal  f (2l-3)
    for f in [1..Int(maxfl/5)] do
      if Value(GFOrderSimp("D", Int((maxfl/f+3)/2)), p^f) mod d = 0 then
        Add(res, [p^f, "D", Int((maxfl/f+3)/2)]);
      fi;
    od;
    for f in [1..Int(maxfl/5)] do
      if Value(GFOrderSimp("D", Int((maxfl/f+3)/2), 2), p^f) mod d = 0 then
        Add(res, [p^f, "2D", Int((maxfl/f+3)/2)]);
      fi;
    od;
    # type G_2(q), degree in non-def. char. > q^2-q-1
    f := 1;
    while p^(2*f)-p^f - 1 <= bnd do
      if Value(GFOrderSimp("G", 2), p^f) mod d = 0 then
        Add(res, [p^f, "G", 2]);
      fi;
      f := f+1;
    od;
    # type 3D_4(q), degree in non-def. char. > q^3(q^2-1)-1
    f := 1;
    while p^(3*f)*(p^(2*f)-1)-1 <= bnd do
      if Value(GFOrderSimp("D", 4, 3), p^f) mod d = 0 then
        Add(res, [p^f, "3D", 4]);
      fi;
      f := f+1;
    od;
    # type F_4(q), degree in non-def. char. > q^8/6
    f := 1;
    while p^(8*f)/6 <= bnd do
      if Value(GFOrderSimp("F", 4), p^f) mod d = 0 then
        Add(res, [p^f, "F", 4]);
      fi;
      f := f+1;
    od;
    # type E_6(q) and 2E_6(q), degree in non-def. char. > q^11/2
    f := 1;
    while p^(11*f)/2 <= bnd do
      if Value(GFOrderSimp("E", 6), p^f) mod d = 0 then
        Add(res, [p^f, "E", 6]);
      fi;
      if Value(GFOrderSimp("E", 6, 2), p^f) mod d = 0 then
        Add(res, [p^f, "2E", 6]);
      fi;
      f := f+1;
    od;
    # type E_7(q), degree in non-def. char. > q^17/2
    f := 1;
    while p^(17*f)/2 <= bnd do
      if Value(GFOrderSimp("E", 7), p^f) mod d = 0 then
        Add(res, [p^f, "E", 7]);
      fi;
      f := f+1;
    od;
    # type E_8(q), degree in non-def. char. > q^29/2
    f := 1;
    while p^(29*f)/2 <= bnd do
      if Value(GFOrderSimp("E", 8), p^f) mod d = 0 then
        Add(res, [p^f, "E", 8]);
      fi;
      f := f+1;
    od;
    p := NextPrimeInt(p);
    # for bigger p only A_1(p) remains, this is handled next
  until p^2 > 2*bnd+2;
##    until p > 2*bnd+2;
  # Sz = 2B_2(q^2), degree in non-def. char. > (q^3)/2
  p := 2;
  f := 1;
  while p^(3*f)/4 < bnd^2 do
    if Value(q^5-q^4+q^3-q^2, p^f) mod d = 0 then
      Add(res, [p^f, "2B", 2]);
    fi;
    f := f+2;
  od;
  # ree = 2G_2(q^2), degree in non-def. char. > (q^4)/2
  p := 3;
  f := 1;
  while p^(2*f)/2 < bnd do
    if Value(q^7-q^6+q^4-q^3, p^f) mod d = 0 then
      Add(res, [p^f, "2G", 2]);
    fi;
    f := f+2;
  od;
  # Ree = 2F_4(q^2), degree in non-def. char. > (q^11)/2
  p := 2;
  f := 1;
  while p^(11*f)/4 < bnd^2 do
    if Value(q^26-q^25+q^23-2*q^22+q^21+q^20-2*q^19+q^18+q^17-2*q^16+q^15-q^13+q^12, p^f) mod d = 0 then
      Add(res, [p^f, "2F", 4]);
    fi;
    f := f+2;
  od;

  return res;
end;

FrequentOrdersSimp := function(ser, rk, F0ord, q)
  local n, d, res;
  if Length(ser) > 1 and ser[1] in "23" then
    F0ord := INT_CHAR(ser[1])-48;
    ser := ser{[2..Length(ser)]};
  fi;
  if ser in ["A","~A"] and F0ord = 1 then
    n := rk+1;
    d := (q^n-1)/(q-1);
    res := [ [d/GcdInt(q-1,n), Phi(d)/d/n ] ];
  elif ser in ["B","C"] then
    d := Gcd(q-1,2);
    res := [[(q^rk-1)/d, Phi(q^rk-1)/2/rk/(q^rk-1)],
            [(q^rk+1)/d, Phi(q^rk+1)/2/rk/(q^rk+1)]];
  elif ser in ["D","~D"] and F0ord = 1 then
    d := Gcd(4,q-1);
    if rk mod 2 = 1 or d = 1 then
      res := [[(q^rk-1)/d, Phi(q^rk-1)/rk/(q^rk-1)]];
    else
      res := [[(q^rk-1)/4, Phi((q^rk-1)/2)/rk/(q^rk-1)*2]];
    fi;
  else
    res := fail;
  fi;
  return res;
end;


RandomProjectiveOrders := function(G, r)
  return List([1..r], i-> ProjectiveOrder(PseudoRandom(G))[1]);
end;
RandomOrders := function(G, r)
  return List([1..r], i-> Order(PseudoRandom(G)));
end;
ro := RandomProjectiveOrders;

testPossibleCrossCharTypes := function(typ, rk, q, dim)
  local g, i, mm, nonew, o, mm1, ords, possibleChars;
  if typ in ["A","~A"] then
    g := SL(rk+1, q);
  elif typ in ["2A","2~A"] then
    g := SU(rk+1, q);
  elif typ = "C" then
    g := Sp(2*rk, q);
  elif typ = "B" then
    g := DerivedSubgroup(SO(2*rk+1, q));
  elif typ in ["D","~D"] then
    g := DerivedSubgroup(SO(2*rk, q));
  else
    return fail;
  fi;
  if dim = 0 then
    dim := MinimalDimBoundCrossCharSimp(typ, rk, 1, q);
  fi;
  i := 0;
  mm := PossibleCrossCharTypes([1], dim);
  nonew := 0;
  ords := [];
  while i < 300 do
    i := i+1;
    o := ProjectiveOrder(PseudoRandom(g))[1];
    Add(ords, o);
    mm1 := PossibleCrossCharTypes([o], mm);
    if mm1=mm then
      nonew := nonew+1;
    else
      nonew := 0;
    fi;
    mm := mm1;
    # the possible characteristics (i.e. primes)
    possibleChars := Set(mm, a -> SmallestRootInt(a[1])); 
    if nonew = 30 then
      return [i-29, possibleChars, ords{[1..i-29]}, mm];
    elif Length(x) = 1 then
      return [i, possibleChars, ords, mm];
    fi;
  od;
  return [i, possibleChars, ords, mm];
end;

MakeGroups := function(dat)
  local q, typ, rk, res, l;
  q := dat[1];
  typ := dat[2];
  rk := dat[3];
  if IsInt(rk) then
    rk := [rk];
  fi;
  res := [];
  if typ = "A" then
    for l in rk do
      Add(res, SL(l+1,q));
    od;
  elif typ = "2A" then
    for l in rk do
      Add(res, SU(l+1,q));
    od;
  elif typ = "C" then
    for l in rk do
      Add(res, Sp(2*l,q));
    od;
  elif typ = "2B" then
    Add(res, SuzukiGroup(q));
  elif typ = "2G" then
    Add(res, Ree(q));
  elif dat = [2,"G",2] then
    Add(res, Group(AtlasGenerators("U3(3).2",1).generators));
  elif typ = "B" and q mod 2 = 0 then
    for l in rk do
      Add(res, Sp(2*l, q));
    od;
  elif dat = [3,"G",2] then
    Add(res, Group(AtlasGenerators("G2(3)",1).generators));
  elif dat = [ 2, "D", [ 4 ] ] then
    Add(res, SO(1,8,2));
  elif dat = [ 2, "2D", [ 4 ] ] then
    Add(res, SO(-1,8,2));
  elif dat = [ 2, "3D", 4 ] then
    Add(res, Group(AtlasGenerators("3D4(2)",1).generators));
  elif dat = [ 4, "G", 2 ] then
    Add(res, Group(AtlasGenerators("G2(4)",1).generators));
  elif dat = [ 3, "B", [ 3 ] ] then
    Add(res, Group(AtlasGenerators("2.O7(3)",1).generators));
  elif dat = [ 2, "F", 4 ] then
    Add(res, Group(AtlasGenerators("F4(2)",2).generators));
  elif dat = [ 2, "2F", 4 ] then
    Add(res, Group(AtlasGenerators("2F4(2)'",1).generators));
  else
    return dat;
  fi;
  return res;
end;


# kleine nicht einfache Gruppen, exzeptionelle Überlagerungen machen !!!!






