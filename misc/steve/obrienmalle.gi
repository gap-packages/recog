# GAP translation attempt Jan 2004 SL

#**************************************************************/
#   Identify the non-abelian simple composition factor        */
#   of a nearly simple matrix group.                          */
#   Uses:  element orders, involution centralizers            */
#                                                             */
#   Step 1: Determine possible underlying characteristic      */
#           (recursively constructing small invol. central.)  */
#                                                             */
#   Step 2: Identify Lie type groups using LieType ()         */
#                                                             */
#   Step 3: Determine degree (if alternating)                 */
#                                                             */
#   Step 4: Determine sporadic candidates                     */
#                                                             */
#    Gunter Malle & E.A. O'Brien                   March 2001 */
#**************************************************************/

#  SetVerbose ("STCS", 1);

NMR_GENS := 12;
NMR_COMM := 6;
NR1 := 30;
NR2 := 30;
NRINV := 150; # if no element of even order found after NRINV tries,
              # assume characteristic 2 type group

Commutators := function (l1, l2)
    return Union(List(l1,x->Set(l2,y->Comm(x,y))));
end;  # Commutators

ProbablyGroupExponent := function (G)
    local   l,  i,  orders,  g,  o,  m;
    l := [1];
    i := 1;
    orders := [];
   repeat
      g := PseudoRandom (G);
      o := Order (g);
      AddSet(orders,o);
      l[i+1] := Lcm (l[i], o);
      i := i+1;
      m := Maximum ([1, i - 10]);
  until (i > 10) and l[i] = l[m];
  return [l[i], orders];
end;  # GroupExponent

RandomGensDerived := function (G)
    local   gens,  i,  g1,  g2;
   gens := [];
   for i in [1..NMR_COMM] do
       g1 := PseudoRandom (G);
       g2 := PseudoRandom (G);
       AddSet(gens,Comm(g1,g2));
   od;
   return gens;
end;  # RandomGensCommutator

InvolutionModCenter := function (G, g)
    local   o,  x;
    o := Order (g);
    if o mod 2 = 0 then
        while o mod 2 = 0 do
            o := o/2;
        od;
        g := g^o;
        if ForAll(GeneratorsOfGroup(G), i->g*i=i*g) then
            return One (G);
        fi;
        for x in GeneratorsOfGroup (G) do
            while g^2*x <> x*g^2 do
                g := g^2;
            od;
        od;
        return g;
    fi;
    return One (G);
end;

RandomInvModCenter := function (G)
    local   i,  g,  o;
    for i in [1..NRINV] do
        g := PseudoRandom (G);
        o := PossiblyProjectiveOrder (g);
        g := InvolutionModCenter (G, g);
        if not IsOne(g) then
            return [g, true];
        fi;
    od;
    return [One(G), false];  # No involution found
end;    # RandomInvModCenter

FindFieldSize := function (H, dim)
    local   o,  qs,  i,  ree;
   o := ProbablyGroupExponent ( H )[1];
   qs := [];
   for i in [o+1, o-1] do
       if IsPrimePowerInt(i) then
           AddSet(qs,i);
       fi;
   od;
   ree := false;
   if dim = 2 then
       if IsPrimePowerInt(2*o-1) and 2*o-1 mod 3 = 0 then
           ree := true;
       fi;
   fi;      # to recognize the Ree groups
   if (dim = 1) or ree then
       for i in [2*o+1, 2*o-1] do
           if IsPrimePowerInt(i) then
               AddSet(qs,i);
           fi;
       od;
   fi;
   if o = 12 then
       AddSet(qs,3);
       return [qs, false];
   fi;     # it may be L2 (3)
   return [qs, true];
end;

# recognize an L2 (q), given a list of possible q's */
WhichL2q := function (G, qs)
    local   orders,  maxord,  q,  p;
    orders := List([1..NR1], i->PossiblyProjectiveOrder(PseudoRandom(G)));
    #some random orders
    maxord := Maximum (orders);
    for q in qs do
        p := Factors(q)[1];
        if ForAny(orders, o->2*p mod o <> 0 and (q+1) mod o <> 0 and
                  (q-1) mod o <> 0) then
            RemoveSet(qs,q);
        fi;
    od;
    if not (4 in orders or 8 in orders) then  RemoveSet(qs,9); fi;
    if not (5 in orders or 10 in orders) then RemoveSet(qs, 5); fi;
    return qs;
end;        # WhichL2q

#  Find a small involution centralizer     */


SmallCentralizer := function (G)
    local   G0,  dim,  tmp,  r1,  flag,  invs,  jf,  g,  h,  x,  o,
            H,  cc,  oG,  xx,  yy;
    G0 := G;
    dim := 0;
    repeat
        tmp :=  RandomInvModCenter(G);
        r1 := tmp[1];
        flag := tmp[2];
        if not flag then
            return [G, 0, G, false];
        fi;
        invs := [];
        for jf in [1..NMR_GENS] do
            g := PseudoRandom (G);
            h := r1*r1^g;
            x := InvolutionModCenter (G, h);
            if x <> One(G) then
                Add(invs, x);
            else   # element has odd order mod center
                o := PossiblyProjectiveOrder (h);
                while o mod 2 = 0 do o := o/2; od;
                Add (invs, h^ ((o+1)/ 2)/g);
            fi;
        od;
        if invs <> [] then
            dim := dim +1;
            H := SubgroupNC(G0,invs);
            cc := RandomGensDerived (H);
            oG := G;
            G := SubgroupNC(G0,cc);
            xx := RandomGensDerived (G);
            G := SubgroupNC(G0, xx);
            yy := Commutators ( xx, cc );
            if ForAll(yy,i->Order(i)=1) then
                return [oG, dim, H, true];  # L2 (q), D_{q+-1}
            fi;
        fi;
    until false;
    Error( "Error: SmallCentralizer failed!");
    return [G, -1, H];
end;    # SmallCentralizer

# given group G, determine its defining field */
DetermineFieldSize := function (G)
    local   tmp,  qs;
    tmp := SmallCentralizer (G);
    qs := FindFieldSize (tmp[3], tmp[2]);
    return qs;
end;

RemoveSome := function (types, ns, orders)

  if ns = 7 and not 6 in orders then
     ns := 0;
  fi;
  if ns = 9 then
      if 15 in orders then
          RemoveSome(types, "U_4 ( 3 )");
      else
          ns := 0;
      fi;
  fi;
  if ns >= 19 then
     if ForAny(orders, o-> not o in  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
                16, 17, 18, 19, 20, 21, 22, 24, 28, 30, 33, 35]) then
         RemoveSet( types,"2E_6 ( 2 )");
     fi;
 fi;
 return [types, ns];
end;   # RemoveSome

DegreeAlternating := function (orders)
    local   degs,  prims,  m,  f,  n;
    degs := [];
    prims := [];
    for m in orders do
        if m > 1 then
            f := Collected(Factors(m));
            Sort(f);
            n := Sum(f, x->x[1]^x[2]);
            if f[1][1] = 2 then n := n+2; fi;
            AddSet(degs,n);
            UniteSet(prims,Set(f,x->x[1]));
        fi;
    od;
    return [degs, prims];
end;    #  DegreeAlternating

RecognizeAlternating := function (orders)
    local   tmp,  degs,  prims,  mindeg,  p1,  p2,  i;
   tmp := DegreeAlternating (orders);
   degs := tmp[1];
   prims := tmp[2];
   if Length(degs) = 0 then
       return "Unknown";
   fi;
   mindeg := Maximum (degs);  # minimal possible degree

   p1 := PrevPrimeInt (mindeg + 1);
   p2 := PrevPrimeInt (p1);
   if not p1 in prims or not p2 in prims then
       return 0;
   fi;
   if mindeg mod 2 = 1 then
       if not (mindeg in orders and  mindeg - 2 in orders) then
           return 0;
       fi;
   else
       if not mindeg - 1 in orders then
           return 0;
       fi;
   fi;

   for i in [3..Minimum (QuoInt(mindeg,2) - 1, 6)] do
       if IsPrime (i) and IsPrime (mindeg - i) then
           if not i * (mindeg - i) in orders then
               return 0;
           fi;
       elif IsPrime (i) and IsPrime (mindeg - i -1) then
           if not i * (mindeg - i - 1) in orders then
               return 0;
           fi;
       fi;
   od;
   return  mindeg;
end;   # RecognizeAlternating

RecogniseAlternating := RecognizeAlternating;

SporadicGroupData := [
                      rec( req := [5,6,8,11],
                           allowed := [],
                           name := "M_11"),
                      rec( req := [6,8,10,11],
                           allowed := [],
                           name := "M_12"),
                      rec( req := [5,6,7,8,11],
                           allowed := [],
                           name := "M_22"),
                      rec( req := [11,14,15,23],
                           allowed := [6,8],
                           name := "M_23"),
                      rec( req := [11,21,23],
                           allowed := [8,10,12,14,15],
                           name := "M_24"),
                      rec( req := [11,15,19],
                           allowed := [6,7,10],
                           name := "J_1"),
                      rec( req := [7,12,15],
                           allowed := [8,10],
                           name := "J_2"),
                      rec( req := [15,17,19],
                           allowed := [8,9,10,12],
                           name := "J_3"),
                      rec( req := [11,20],
                           allowed := [7,8,10,12,15],
                           name := "HS"),
                      rec( req := [11,14,30],
                           allowed := [8,9,12],
                           name := "McL"),
                      rec( req := [11,13],
                           allowed := [14,15,18,20,21,24],
                           name := "Suz"),
                      rec( req := [26,29],
                           allowed := [14,15,16,20,24],
                           name := "Ru"),
                      rec( req := [22,23,24,30],
                           allowed := [14,18,20,21],
                           name := "Co_3"),
                      rec( req := [16,23,28,30],
                           allowed := [11,18,20,24],
                           name := "Co_2"),
                      rec( req := [33,42],
                           allowed := [16,22,23,24,26,28,35,36,39,40,60],
                           name := "Co_1"),
                      rec( req := [19,28,31],
                           allowed := [11,12,15,16,19,20,28,31],
                           name := "ON"),
                      rec( req := [13,24,30],
                           allowed := [14,16,18,20,21,22],
                           name := "Fi_22"),
                      rec( req := [17,28],
                           allowed := [8,10,12,15,21],
                           name := "He"),
                      rec( req := [31,67],
                           allowed := [18,22,24,25,28,30,33,37,40,42],
                           name := "Ly"),
                      rec( req := [37,43],
                           allowed := [16,23,24,28,29,30,31,33,35,40,42,44,66],
                           name := "J_4")];
                           # is 15 not needed here?



RecognizeSporadic := function (orders)
    local   maxords,  spors,  r;
    orders := Set(orders);
    maxords := Filtered(orders, i-> Number(orders,j -> j mod i = 0)=1);
    spors := [];
    for r in SporadicGroupData do
        if ForAll(r.req, o->o in maxords) and
           ForAll(maxords, o->o in r.allowed or o in r.req) then
            Add(spors,r.name);
        fi;
    od;
  return spors;
end;  # RecognizeSporadic

RecogniseSporadic := RecognizeSporadic;

IdentifySimple := function (G0)
    local   NmrTries,  limit,  d,  orders,  NRtries,  ct,  tmp,  G,
            dim,  H,  flag,  qs,  flag2,  ps,  types,  p,  erg,  ns,
            spors, deg;

    NmrTries := ValueOption("NmrTries");
    if NmrTries = fail then
        NmrTries := 15;
    fi;

    if IsMatrixGroup(G0) then
        deg := DimensionOfMatrixGroup(G0);
    else
        deg := 100;
    fi;

#  /* replace G0 by successive terms of its derived series
#     until we obtain a perfect group; if there are more
#     than 3 iterations, then we can conclude that
#     G/Z (F^* (G)) is probably not almost simple */

    limit := 0;
    while IsProbablyPerfect (G0) = false and limit < 4 do
        limit := limit + 1;
        G0 := DerivedSubgroupApproximation (G0);
        if IsTrivial(G0)  then
            return [false];
        fi;
    od;

    if limit > 4 then
        return [false, "G0 is not quasi-simple"];
    fi;

    if IsMatrixGroup(G0) then
        d := DimensionOfMatrixGroup(G0);
    else
        d := 100; # I dunno
    fi;
    orders := [];
    NRtries := 0;
    repeat
        NRtries := NRtries + 1;
        ct := 0;
        repeat
            tmp := SmallCentralizer (G0);
            G := tmp[1];
            dim := tmp[2];
            H := tmp[3];
            flag := tmp[4];
            if flag then
                tmp :=  FindFieldSize(H, dim);
                qs := tmp[1];
                flag2 := tmp[2];
                qs := WhichL2q (G, qs);
                ct := ct + 1;
            else
                qs := [2];
            fi;
        until Length(qs) >= 1 or ct >= 6;

        UniteSet(orders,Set([1..NR2 + 4*d], i-> PossiblyProjectiveOrder(PseudoRandom(G0))));
        ps := Set(qs, q->Factors(q)[1]);
        AddSet(ps,2);
        types := [];
        for p in ps do
            erg := LieType (G0, p, orders, 30 + 10 *  deg);
            if not IsRecognitionOutcome(erg) then
                AddSet(types,erg);
            fi;
        od;

        ns := RecognizeAlternating (orders);
        if ns <> "Unknown" then
            tmp := RemoveSome (types, ns, orders);
            types := tmp[1];
            ns := tmp[2];
            if ns <> 0 then
                AddSet(types,Concatenation("A_",String(ns)));
            fi;
        fi;

        spors := RecognizeSporadic (orders);
        types := Union(types, spors);

        if Length(types) >= 1 then
            if  Length(types) = 1 then
                return [true, types[1]];
            else
                return [true, types];
            fi;
        fi;
    until Length(types) > 0 or NRtries > NmrTries;

    Print("Not recognized after ", NmrTries, " tries; qs = ",qs,"\n");
    return [false];

end;  # IdentifySimple


InstallNonConstructiveRecognizer(function(g)
    local   res;
    res := IdentifySimple(g);
    if res[1] = true then
        RecognitionInfo(g).Name := res[2];
        return res[2];
    else
        return RO_NO_LUCK;
    fi;
end,
  "Malle and O'Brien code translated into GAP");
