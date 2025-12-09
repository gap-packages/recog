#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This files's authors include Max Neunhöffer, Ákos Seress.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
##
##  Recognise quasi-simple group of Lie type when characteristic is known.
##
##  [BKPS02] & [AB01] provide theoretical basis for algorithms.
##
##  This version developed by Malle & O'Brien March 2001, convert to GAP by
##  Steve Linton.
##
#############################################################################

# GAP translation attempt Jan 2004 SL

RECOG.LieTypeOrderFunc := RECOG.ProjectiveOrder;
RECOG.LieTypeSampleSize := 250;
RECOG.LieTypeNmrTrials := 10;

RECOG.OMppdset := function(p, o)
    local   primes;
    primes := Set(Factors(o));
    RemoveSet(primes,p);
    return Set(primes, l->OrderMod(p,l));
end;

RECOG.VerifyOrders := function (type, n, q, orders)
    local   p,  allowed,  maxprime,  r,  rq,  ii, LargestPrimeOccurs;
    LargestPrimeOccurs := function(r, orders)
        local   maxp;
        maxp := Maximum(Factors(r));
        return ForAny(orders, i->i mod maxp = 0);
    end;
    p := Factors(q)[1];
    allowed := orders;
    maxprime := true;
    if type = "L" then
        if n = 2 then
            if p = 2 then
                allowed := Set([2, q-1, q+1]);
            else
                allowed := Set([p, (q-1)/2, (q+1)/2]);
          fi;
      elif n = 3 then
          if (q-1) mod 3 <> 0 then
              allowed := Set([4, p* (q-1), q^2-1, q^2+q+1]);
          else
              allowed := Set([4, p* (q-1)/3, q-1, (q^2-1)/3, (q^2+q+1)/3]);
          fi;
      elif n = 4 then
          if p = 2 then
              allowed := Set([4* (q-1), p* (q^2-1), q^3-1, (q^2+1)* (q-1),
                              (q^2+1)* (q+1)]);
          elif p = 3 then
              allowed := Set([9, p* (q^2-1), q^3-1, (q^2+1)* (q-1),
                              (q^2+1)* (q+1)]);
          elif (q-1) mod 2 <> 0 then
              allowed := Set([p*(q^2-1),q^3-1,(q^2+1)* (q-1), (q^2+1)* (q+1)]);
          elif (q-1) mod 4 = 2 then
              allowed := Set([p* (q^2-1), (q^3-1)/2, (q^2+1)* (q-1)/2,
                              (q^2+1)* (q+1)/2 ]);
          else
              allowed := Set([p* (q^2-1), (q^3-1)/4, (q^2+1)* (q-1)/4,
                              (q^2+1)* (q+1)/4 ]);
          fi;
      elif n = 5 and q = 2 then
          allowed := Set([8, 12, 14, 15, 21, 31]);
      elif n = 6 and q = 3 then
          allowed := Set([36, 78, 80, 104, 120, 121, 182]);
          maxprime := 91 in orders or 121 in orders;
      else
          maxprime := LargestPrimeOccurs (q^n-1, orders)
                      and LargestPrimeOccurs (q^(n-1)-1, orders)
                      and Maximum (orders) <= (q^n-1)/ (q-1)/Gcd (n,q-1);
          if n = 8 and q = 2 then
              maxprime := maxprime and LargestPrimeOccurs (7, orders);
              #/Set([ i : i in orders | i mod 21 = 0]) <> Set([]);
          fi;
      fi;
  elif type = "U" then
      if n = 3 then
          if (q+1) mod 3 <> 0 then
              allowed := Set([4, p* (q+1), q^2-1, q^2-q+1]);
          else
              allowed := Set([4, p* (q+1)/3, q+1, (q^2-1)/3, (q^2-q+1)/3]);
          fi;
      elif n = 4 then
          if p = 2 then
              allowed := Set([8, 4* (q+1), p* (q^2-1), q^3+1, (q^2+1)* (q-1),
                              (q^2+1)* (q+1)]);
          elif p = 3 then
              allowed := Set([9, p* (q^2-1), q^3+1, (q^2+1)* (q-1),
                              (q^2+1)* (q+1)]);
              if q = 3 then
                  maxprime := 8 in orders and 9 in orders;
              fi;
          elif (q+1) mod 2 <> 0 then
              allowed := Set([p*(q^2-1),q^3+1,(q^2+1)* (q-1), (q^2+1)* (q+1)]);
          elif (q+1) mod 4 = 2 then
              allowed := Set([p* (q^2-1), (q^3+1)/2, (q^2+1)* (q-1)/2,
                              (q^2+1)* (q+1)/2 ]);
              if q = 5 then
                  maxprime := Maximum (orders) > 21;
              fi;
          else
              allowed := Set([p* (q^2-1), (q^3+1)/4, (q^2+1)* (q-1)/4,
                              (q^2+1)* (q+1)/4 ]);
          fi;
      else
          r := 2 * ((n-1)/2)+1;
          maxprime := LargestPrimeOccurs (q^r+1, orders)
                      and Maximum (orders) <= (q^(r+1)-1)/ (q-1);
          if n = 6 and q = 2 then
              maxprime := maxprime and 18 in orders;
          fi;
      fi;
  elif type = "S" then
      if n = 4 then
          if q mod 2 = 0 then
              allowed := Set([4, p * (q-1), p * (q+1), q^2-1, q^2+1]);
          elif q mod 3 = 0 then
              allowed := Set([9, p * (q-1), p * (q+1), (q^2-1)/2, (q^2+1)/2]);
          else
              allowed := Set([p * (q-1), p * (q+1), (q^2-1)/2, (q^2+1)/2]);
          fi;
      elif n = 6 and q = 2 then
          allowed := Set([ 7, 8, 9, 10, 12, 15 ]);
          maxprime := 8 in orders and 15 in orders;
      else
          maxprime := LargestPrimeOccurs (q^(n/2)+1, orders) and
                      LargestPrimeOccurs (q^(n/2)-1, orders);
      fi;
  elif type = "O^+" and n = 8 and q = 2 then
      allowed := Set([ 7, 8, 9, 10, 12, 15 ]);
      maxprime := 8 in orders and 15 in orders;
  elif type = "O^+" and n = 10 and q = 2 then
      allowed := Set([ 18, 24, 31, 42, 45, 51, 60]);
  elif type = "O^-" then
      maxprime := LargestPrimeOccurs (q^(n/2)+1, orders) and
                  LargestPrimeOccurs (q^(n/2 -1)-1, orders);
  elif type = "2B" then
      rq := RootInt(2*q);
      allowed := Set([4, q-1, q-rq+1, q+rq+1]);
  elif type = "2G" then
      rq := RootInt(3*q);
      allowed := Set([9, 3* (q-1), q+1, q-rq+1, q+rq+1]);
  elif type = "G" then
      if p = 2 then
          allowed := Set([8, 4 * (q-1), 4 * (q+1), q^2-1, q^2-q+1, q^2+q+1]);
      elif p <= 5 then
          allowed := Set([p^2, p * (q-1), p * (q+1), q^2-1, q^2-q+1, q^2+q+1]);
      else
          allowed := Set([p * (q-1), p * (q+1), q^2-1, q^2-q+1, q^2+q+1]);
      fi;
  elif type = "2F" and q = 2 then
      allowed := Set([10, 12, 13, 16 ]);
  elif type = "2F" and q = 8 then
      allowed := Set([ 12, 16, 18, 20, 28, 35, 37, 52, 57, 63, 65, 91, 109 ]);
      maxprime := Maximum (orders) > 37;
  elif type = "3D" and q = 2 then
      allowed := Set([ 8, 12, 13, 18, 21, 28 ]);
      maxprime := Maximum (orders) > 13;
  elif type = "F" and q = 2 then
      allowed := Set([ 13, 16, 17, 18, 20, 21, 24, 28, 30 ]);
  elif type = "2E" and q = 2 then
      allowed := Set([ 13, 16, 17, 18, 19, 20, 21, 22, 24, 28, 30, 33, 35 ]);
  elif type = "E" and n = 7 and q = 2 then
      maxprime := Maximum (orders) <= 255;
  fi;

  if not maxprime then
      return "RO_CONTRADICTION";
  fi;
  for ii in allowed do
      orders := Filtered( orders, o-> ii mod o <> 0 );
  od;
  if orders = [] then
      return Concatenation(type,String(n), "(", String(q), ")");
  else
      return  "RO_CONTRADICTION";
  fi;
end;  #  VerifyOrders

#/*  P random process for group;
#    distinguish PSp (2n, p^e) from Omega (2n + 1, p^e);
#    orders are orders of elements */
#

RECOG.DistinguishSpO := function (G, n, p, e, orders)
    local   twopart,   q,  goodtorus,  t1,  tp,  t2,
            found,  tf,  ttf,  g,  o,  mp,  i,  x,  z,  po,  h;

    twopart := function (n)
        local k;
        k := 1;
        while n mod 2 = 0 do
            n := n/2;
            k := k*2;
        od;
        return k;
    end;

    q := p^e;
    if n mod 2 = 1 and (q + 1) mod 4 = 0 then
        goodtorus := 2 * n;
        t1 := q^n + 1;
        tp := twopart ((q^n + 1) / 2);
    else
        goodtorus := n;
        t1 := q^n - 1;
        tp := twopart ((q^n - 1) / 2);
    fi;
    t2 := q^QuoInt(n , 2) + 1;

    found := false;
    tf := 0; ttf := 0;  # counters to deal with wrong char groups
    repeat
        g := PseudoRandom (G);
        o := RECOG.LieTypeOrderFunc (g);
        if o mod p <> 0 then
            ttf := ttf+1;
            mp := RECOG.OMppdset (p, o);


            if 2*o = t1 then
                tf := tf+1;
                g := g^(o / 2);
                found := n mod 2 = 1;
                i := 0;
                while not found and i < 8 * n do
                    i := i+1;
                    x := PseudoRandom (G);
                    z := g * g^x;
                    o := RECOG.LieTypeOrderFunc (z);
                    if o mod 2 = 1 then
                        po := RECOG.LieTypeOrderFunc (z^((o + 1) / 2) / x);
                        mp := RECOG.OMppdset (p, po);
                        if (q - 1) mod 4 = 0 and (n - 1) * e in mp or
                           (q + 1) mod 4 = 0 and 2 * (n - 1) * e in mp or
                           (q - 1) mod 4 = 0 and 2 * (n - 1) * e in mp or
                           (q + 1) mod 4 = 0 and 2 * n * e in mp
#                              or (n = 4 and 6 in mp)
                           then
                            found := true;
                  #printf"mp= %o, o (z)= %o\n", mp, Factorization (oo);
                        fi;
                    fi;
                od;
            fi;
        fi;
    until found or (tf > 15) or (ttf > 80);
    if ttf > 80 then
        return "RO_NO_LUCK";
    fi;

    for i in [1..6 * n] do
        h := PseudoRandom (G);
        o := Order (g * g^h);
        if (q * (q + 1) mod o <> 0) and (q * (q - 1) mod o <> 0)
           then
            return RECOG.VerifyOrders ("S", 2 * n, q, orders);
        fi;
    od;

    return RECOG.VerifyOrders ("O", 2 * n + 1, q, orders);

end;   # DistinguishSpO

#
#/* compute Artin invariants for element of order o;
#   p is characteristic */

RECOG.ComputeArtin := function (o, p)
    local   IsFermat,  IsMersenne,  primes,  orders;
    IsFermat := n-> IsPrime(n) and Set(Factors(n-1)) = [2];
    IsMersenne := n->IsPrime(n) and Set(Factors(n+1)) = [2];
    primes := Set(Factors(o));
    RemoveSet(primes,p);
    RemoveSet(primes,2);
    orders := Set(primes, x-> OrderMod(p, x));

    if IsFermat (p) and o mod 4 = 0 then
        AddSet(orders,1);
    fi;
    if IsMersenne (p) and o mod 4 = 0 then
        AddSet(orders,2);
    fi;
    if p = 2 and o mod 9 = 0 then
        AddSet(orders, 6);
    fi;
    return orders;
end;

#/* partition at most Nmr elements according to their
#   projective orders listed in values; we consider
#   at most NmrTries elements; P is a random process */

RECOG.ppdSample := function (G, ppd, p, values, SampleSize)
    local   Bins,  x,  j,  original,  NmrTries,  g,  o,  list;

    Bins := ListWithIdenticalEntries(Length(values),0);

   for x in ppd do
       for j in [1..Length(values)] do
           if values[j] in x then
               Bins[j] := Bins[j] + 1;
           fi;
       od;
   od;
   original := Length(ppd);

   ppd := [];

   NmrTries := 0;
   while NmrTries <= SampleSize do
       NmrTries := NmrTries + 1;
       g := PseudoRandom (G);
       o := Order (g);
       list := RECOG.ComputeArtin (o, p);
       Add (ppd, list);
       for j in [1..Length(values)] do
           if values[j] in list then
               Bins[j] := Bins[j]+1;
           fi;
       od;
   od;


   return [Bins/(original + SampleSize), ppd, Bins];

end;

RECOG.OrderSample := function (G, p, orders, values, SampleSize)
    local    Bins,  i,  j,  original,  NmrTries,  g,  o,
            Total;

    Bins := ListWithIdenticalEntries(Length(values),0);

   for i in orders do
      for j in [1..Length(values)] do
         if i mod values[j] = 0 then
            Bins[j] := Bins[j] + 1;
         fi;
      od;
   od;
   original := Length(orders);

   NmrTries := 0;
   while NmrTries <= SampleSize do
      NmrTries := NmrTries + 1;
      g := PseudoRandom (G);
      o := RECOG.LieTypeOrderFunc (g);
      Add (orders, o);
      for j in [1..Length(values)] do
         if o mod values[j] = 0 then
            Bins[j] := Bins[j]+1;
         fi;
      od;
      Total := Sum(Bins);
   od;

   return [ Bins/ (SampleSize + original), orders, Bins] ;

end;

# PSL (2, p^k) vs PSp (4, p^(k / 2))
RECOG.PSLvsPSP := function (G, ppd, q, SampleSize, NmrTrials, orders)
    local   p,  g,  o,  v1,  values,  temp,  prob;
   p := Factors (q)[1];
   if q = 2 then
      repeat
         SampleSize := SampleSize - 1;
         g := PseudoRandom (G);
         o := RECOG.LieTypeOrderFunc (g);
         if o = 4 then
            return RECOG.VerifyOrders ("L",2,9, orders);
         fi;
      until SampleSize = 0;
      return RECOG.VerifyOrders ("L",2,4, orders);
   fi;

   v1 := Maximum (ppd);
   ppd := [];
   values := [v1];
   repeat
       temp := RECOG.ppdSample (G, ppd, p, values, SampleSize);
       prob := temp[1];
       ppd  := temp[2];
       prob := prob[1];
       if prob >= 1/3 and prob < 1/2 then
           return RECOG.VerifyOrders ("L",2, q^2, orders);
       elif prob >= 1/5 and prob < 1/4 then
           return RECOG.VerifyOrders ("S",4, q, orders);
       fi;
       NmrTrials := NmrTrials + 1;
   until NmrTrials = 0;

   if NmrTrials = 0 then
#      return "Have not settled this recognition";
      return "RO_NO_LUCK";
   fi;

end;


RECOG.OPlus82vsS62 := function (G, orders, SampleSize)
    local   values,  temp,  prob;
    values := [15];
    temp := RECOG.OrderSample (G, 2, [], values, SampleSize);
    prob := temp[1];
    orders := temp[2];
    prob := prob[1];
#"prob is ", prob;
    if AbsoluteValue (1/5 - prob) < AbsoluteValue (1/15 - prob) then
        return RECOG.VerifyOrders ("O^+",8, 2, orders );
    else
        return RECOG.VerifyOrders ("S",6, 2, orders );
    fi;
end;

RECOG.OPlus83vsO73vsSP63 := function (G, orders, SampleSize)
    local   values,  temp,  prob;
    values := [20];
    temp := RECOG.OrderSample (G, 3, [], values, SampleSize);
    prob := temp[1];
    orders := temp[2];
    prob := prob[1];
    if AbsoluteValue (3/20 - prob) < AbsoluteValue (1/20 - prob) then
        return "O^+_8(3)";
    else
        return RECOG.DistinguishSpO (G, 3, 3, 1, orders);
    fi;
end;


RECOG.OPlus8vsO7vsSP6 := function (G, orders, p, e, SampleSize)
    local   i,  g,  o,  list;

   for i in [1..SampleSize] do
       g := PseudoRandom (G);
       o := RECOG.LieTypeOrderFunc (g);
       list := RECOG.ComputeArtin (o, p);
       if IsSubset(list, [e, 2 * e, 4 * e]) then
           return RECOG.VerifyOrders ("O^+",8, p^e , orders);
       fi;
   od;
   if p = 2 then
       return RECOG.VerifyOrders ("S",6, 2^e, orders);
   else
       return RECOG.DistinguishSpO (G, 3, p, e, orders);
   fi;
end;


#// O- (8, p^e) vs S (8, p^e) vs O (9, p^e)
RECOG.OMinus8vsSPvsO := function (G, v1, p, e, orders, SampleSize, NmrTrials)
    local   ppd,  values,  epsilon,  temp,  prob;
    ppd := [];
    values := [v1];
    epsilon := 1/50;
    repeat
        temp := RECOG.ppdSample (G, ppd, p, values, SampleSize);
        prob := temp[1];
        ppd := temp[2];
#"prob is ", prob;
        prob := prob[1];
        if prob >= 1/5 - epsilon and prob < 1/4 + epsilon then
            return RECOG.VerifyOrders ("O^-",8, p^(v1/8), orders);
        elif prob >= 1/10 - epsilon and prob < 1/8 + epsilon then
            if p = 2 then
                return RECOG.VerifyOrders ("S",8, 2^e, orders);
            else
                return RECOG.DistinguishSpO (G, 4, p, e, orders);
            fi;
        fi;
        NmrTrials := NmrTrials - 1;
    until NmrTrials = 0;

    if NmrTrials = 0 then
#      return "Have not settled this recognition";
        return "RO_NO_LUCK";
    fi;

end;

RECOG.ArtinInvariants := function (G, p, Nmr)
    local   orders,  combs,  invariants,  newv1,  v1,  i,  g,  o,
            ppds;

    orders := [];
    combs := [];
    if p > 2 then
        invariants := [0, 1, 2];
    else
        invariants := [0, 1];
    fi;
    newv1 := Maximum (invariants);
    repeat
        v1 := newv1;
        for i in [1..Nmr] do
            g := PseudoRandom (G);
            o := RECOG.LieTypeOrderFunc (g);
            AddSet (orders, o);
            if o mod 3 = 0 then
                AddSet(orders,3);
            fi;
            if o mod 4 = 0 then
                AddSet (orders, 4);
            fi;
            ppds := RECOG.OMppdset (p, o);
            if p = 2 and o mod 9 = 0 then
                AddSet (ppds, 6);
                AddSet (orders, 9);
            fi;
            UniteSet(invariants,ppds);
            UniteSet(combs, Combinations (ppds, 2));
        od;
        newv1 := Maximum (invariants);
    until newv1 = v1;
    return [invariants, combs, orders];
end; # ArtinInvariants


RECOG.LieType := function (G, p, orders, Nmr)
    local   temp,  invar,  combs,  orders2,  v1,  v2,  w,  v3,  e,  m,
            bound,  combs2;

    #   P := RandomProcess ( G );
    temp := RECOG.ArtinInvariants (G, p, Nmr);
    invar := temp[1];
    combs := temp[2];
    orders2 := temp[3];
   UniteSet(orders, orders2);

   v1 := Maximum (invar);
   RemoveSet(invar, v1);

   if v1 = 2 then
      return RECOG.VerifyOrders ("L",2, p, orders);
   fi;

   if v1 = 3 then
      if p > 2 then
         return RECOG.VerifyOrders ("L",3, p, orders);
      elif 8 in orders then
         return RECOG.VerifyOrders ("U",3, 3, orders);
      else
         return RECOG.VerifyOrders ("L",3, 2, orders);
      fi;
   fi;


   if v1 = 4 then
      if 3 in invar then
         if p > 2 then
            return RECOG.VerifyOrders ("L",4, p, orders);
         elif 15 in orders then
            return RECOG.VerifyOrders ("L",4, 2, orders);
         else
            return RECOG.VerifyOrders ("L",3, 4, orders);
         fi;
      else
         return RECOG.PSLvsPSP (G, [1, 2, 4], p, RECOG.LieTypeSampleSize,
                   RECOG.LieTypeNmrTrials, orders);
      fi;
   fi;  # v1 = 4

   v2 := Maximum (invar);
   w := v1 / (v1 - v2);

#v1; v2; w; invar; orders;
   if v1 = 12 and v2 = 4 and p = 2 then
      if 21 in orders then
         return RECOG.VerifyOrders ("G",2, 4, orders);
      elif 16 in orders then
         return RECOG.VerifyOrders ("2F",4, 2, orders);
      elif 7 in orders then
         return RECOG.VerifyOrders ("2B",2, 8, orders);
      elif 15 in orders then
         return RECOG.VerifyOrders ("U",3, 4, orders);
      else
          return "RO_CONTRADICTION";
      fi;
   fi;  # v2 = 4

   RemoveSet(invar,v2);
   if Length(invar)  = 0 then
       return "RO_Unknown";
   fi;
   v3 := Maximum (invar);

#printf"p, v1, v2, v3: %o %o %o %o;",p,v1,v2,v3; invar; combs; orders;
   if v1 mod 2 = 1 then
      e := v1 - v2;
      if v1 mod e <> 0 then
         return "RO_CONTRADICTION";
      fi;
      m := v1/e;
      if v3 <> e* (m-2) then
          return "RO_CONTRADICTION";
      fi;
      return RECOG.VerifyOrders ("L", m, p^e, orders);
   fi;

   if w = 3/2 then
      if p = 2 and not 3 in orders then
         if v1 mod 8 <> 4 then
            return "RO_CONTRADICTION";
         fi;
         return RECOG.VerifyOrders ("2B",2,2^(v1 / 4), orders);
      fi;
      if v1 mod 6 <> 0 then
         return "RO_CONTRADICTION";
      fi;
      if p = 3 and not 4 in orders then
         if v1 > 6 then
            if v1 mod 12 <> 6 then
               return "RO_CONTRADICTION";
            fi;
            return RECOG.VerifyOrders ("2G",2, 3^(v1 / 6), orders);
         else
            return RECOG.VerifyOrders ("L",2, 8, orders);
         fi;
      fi;
      return RECOG.VerifyOrders ("U",3, p^(v1 / 6), orders);
   fi;

   if w = 4/3 then
      if p = 2 and v1 mod 8 = 4 then
         return RECOG.VerifyOrders ("2B",2, 2^(v1 / 4), orders);
      fi;
      return "RO_CONTRADICTION";
   fi;

   if w = 2 then  # exceptional groups
      if v1 mod 12 = 0 and not ([v1 / 3, v1] in combs) then
         if 4 * v3 = v1 then
            return RECOG.VerifyOrders ("3D",4, p^(v1 / 12), orders);
         elif (v1 / 4) in invar or (p = 2 and v1 = 24) then
            return RECOG.VerifyOrders ("G",2, p^(v1 / 6), orders);
         else
            if p = 2 and v1 mod 24 = 12 and 12*v3 = 4*v1 then
               return RECOG.VerifyOrders ("2F",4,2^(v1 / 12), orders);
            else return "RO_CONTRADICTION";
            fi;
         fi;

  #    /* next clause is replacement for error in draft of paper */
      elif v1 mod 12 = 6 and Maximum (orders) <= p^(v1/3) + p^(v1/6) + 1 then
         return RECOG.VerifyOrders ("G",2, p^(v1 / 6), orders);
      fi;

      if v1 mod 4 = 2 then
         return RECOG.VerifyOrders ("L",2,p^(v1 / 2), orders);
      else
         return RECOG.PSLvsPSP (G, Union(invar,[v1, v2]),p^(v1 / 4),
                  RECOG.LieTypeSampleSize, RECOG.LieTypeNmrTrials, orders);
      fi;
   fi;  # w = 2

#printf"p, v1, v2, v3: %o %o %o %o;",p,v1,v2,v3; invar; combs; orders;
   if w = 3 then
      if v1 mod 18 = 0 and 18 * v3 = 10 * v1 then
         if 8* (v1 / 18) in invar then
            return RECOG.VerifyOrders ("2E",6, p^(v1 / 18), orders);
         else return "RO_OTHER";
         fi;
      elif v1 mod 12 = 0 then
         if v1 > 12 or p > 2 then
            if v1 = 2 * v3 and not ([v1 / 2, v1] in combs)
               and not ([v1 / 3, v1] in combs) then
               return RECOG.VerifyOrders ("F",4, p^(v1 / 12), orders);
            fi;
         elif 9 in orders and not ([4, 12] in combs) then
            return RECOG.VerifyOrders ("F",4, 2, orders);
         fi;
      fi;
   fi;  # w = 3

   if w = 4 and 8 * v1 = 12 * v3 then
      if v1 mod 12 = 0 then
         return RECOG.VerifyOrders ("E",6, p^(v1 / 12), orders);
      fi;
      return "RO_CONTRADICTION";
   fi;

   if w = 9/2 and 12 * v1 = 18 * v3 then
      if v1 mod 18 = 0 then
         return RECOG.VerifyOrders ("E",7, p^(v1 / 18), orders);
      fi;
      return "RO_CONTRADICTION";
   fi;

   if w = 5 and 20 * v1 = 30 * v3 then
      if v1 mod 30 = 0 then
         return RECOG.VerifyOrders ("E",8, p^(v1 / 30), orders);
      fi;
      return "RO_CONTRADICTION";
   fi;   # exceptional groups

   if v1 mod (v1 - v2) <> 0 then   # unitary groups
      if (v1-v2) mod 4 <> 0  or  2 * v1 mod (v1 - v2) <> 0 then
          return "RO_OTHER";
      fi;
      e := (v1-v2) / 4;
      m := (2 * v1) / (v1 - v2);
      if ((m + 1) mod 4 = 0 and e * (m + 1) in invar) or
        ((m + 1) mod 4 <> 0 and e * (m + 1) / 2 in invar) then
            if (m > 7 and v2-v3 = 4*e) or (m <= 7 and v2-v3 = 2*e) then
               return RECOG.VerifyOrders ("U", m + 1, p^e, orders);
            fi;
      else
         if (m > 5 and v2-v3 = 4*e) or (m = 5 and v2-v3 = 2*e) then
            return RECOG.VerifyOrders ("U", m, p^e, orders);
         fi;
      fi;
      return "RO_OTHER";
   fi;   # unitary groups

#printf"1: v1 v2 v3 = %o %o %o;;",v1, v2, v3; invar;
   if (v1 - v2) mod 2 <> 0 then
      e := v1 - v2;  m := v1 / (v1 - v2);
      if v3 = e* (m-2) or (p = 2 and e* (m-2) = 6) or (m <= 3) then
         return RECOG.VerifyOrders ("L", m, p^e, orders);
      else
         return "RO_OTHER";
      fi;
   fi;

   e := (v1 - v2) / 2; m := v1 / (v1 - v2);  # only classical grps remain

   if p = 2 and e * m = 6 and e <= 2 and 91 in orders then
      if v3 = 10-2*e  or  m = 3 then
         return RECOG.VerifyOrders ("L", m, 2^(2 * e), orders);
      else
         return "RO_OTHER";
      fi;
   fi;

   if Set([m * e, v1]) in combs then
      if v3 = 2*e* (m-2) or m <= 3 then
         return RECOG.VerifyOrders ("L", m, p^(2 * e), orders);
      else
         return "RO_OTHER";
      fi;
   fi;

   if m = 3 then
      if 3 * v3 = v1 then
         return RECOG.VerifyOrders ("U",4, p^(v1 / 6), orders);
      else
         if p^e = 2 then
            return RECOG.OPlus82vsS62 (G, orders, RECOG.LieTypeSampleSize);
         fi;
         if p^e = 3 then
            return RECOG.OPlus83vsO73vsSP63 (G,orders,RECOG.LieTypeSampleSize);
         else
            return RECOG.OPlus8vsO7vsSP6 (G,orders,p,e,RECOG.LieTypeSampleSize);
         fi;
      fi;
   fi;

   if v3 <> 2*e* (m-2) and (m > 4 or v3 <> 5*e) then   # wrong characteristic
      return "RO_OTHER";
   fi;

   if IsMatrixGroup(G) then
       bound := 5*DimensionOfMatrixGroup(G);
   else
       bound := 100;
   fi;
   temp := RECOG.ArtinInvariants (G, p, bound);
   invar := temp[1]; combs2 := temp[2]; orders2 := temp[3];
   combs := Union(combs, combs2);
   orders := Union(orders, orders2);
   if m mod 2 = 0 then
      if [m * e, (m + 2) * e] in combs then
          return RECOG.VerifyOrders ("O^+", 2 * m + 2, p^e, orders);
      elif m = 4 then
         return RECOG.OMinus8vsSPvsO(G,v1,p,e,orders,RECOG.LieTypeSampleSize,
                                     RECOG.LieTypeNmrTrials);
      else #/* m >= 6 */
         if [ (m - 2) * e, (m + 2) * e] in combs then
            if p = 2 then
               return RECOG.VerifyOrders ("S", 2 * m, 2^e, orders);
            else
               return RECOG.DistinguishSpO (G, m, p, e, orders);
            fi;
         else
            return RECOG.VerifyOrders ("O^-", 2*m, p^e, orders);
         fi;
      fi;  # m even
   elif [(m - 1) * e, (m + 3) * e] in combs then
      return RECOG.VerifyOrders ("O^+", 2 * m + 2, p^e, orders);
   elif [(m - 1) * e, (m + 1) * e] in combs then
      if p = 2 then
         return RECOG.VerifyOrders ("S", 2 * m, 2^e, orders);
      fi;
      # p <> 2 case
      return RECOG.DistinguishSpO (G, m, p, e, orders);
   else
      return RECOG.VerifyOrders ("O^-", 2 * m, p^e, orders);
   fi;

   return "RO_undecided";
end;

#! @BeginChunk LieTypeNonConstr
#! Recognise quasi-simple group of Lie type when characteristic is given.
#! Based on <Cite Key="BKPS02"/> and <Cite Key="AB01"/>.
#! @EndChunk
BindRecogMethod(FindHomMethodsProjective, "LieTypeNonConstr",
"do non-constructive recognition of Lie type groups",
function(ri,G)
    local count,dim,f,i,ords,p,q,r,res;
    RECOG.SetPseudoRandomStamp(G,"LieTypeNonConstr");
    dim := ri!.dimension;
    f := ri!.field;
    q := Size(f);
    p := Characteristic(f);

    count := 0;
    ords := Set(ri!.simplesoclerando);
    while true do   # will be left by return
        r := RECOG.LieType(ri!.simplesocle,p,ords,30+10*dim);
        if not IsString(r) or r{[1..3]} <> "RO_" then
            # We found something:
            Info(InfoRecog,2,"LieTypeNonConstr: found ",r,
                 ", lookup up hints...");
            ri!.comment := r;
            res := LookupHintForSimple(ri,G,r);
            # FIXME: LookupHintForSimple is for sporadics... So why do we use it here?
            if res = true then
                return Success;
            fi;
            Info(InfoRecog,2,"LieTypeNonConstr: giving up.");
            return fail;
        fi;
        count := count + 1;
        if count > 3 then
            Info(InfoRecog,2,"LieTypeNonConstr: giving up...");
            return TemporaryFailure;
        fi;
        Info(InfoRecog,2,"LieTypeNonConstr: need more element orders...");
        for i in [1..dim] do
            AddSet(ords,RandomElmOrd(ri,"LieTypeNonConstr",false).order);
        od;
    od;
end);
