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
#############################################################################

# Description of a "fingerprint" of a group G:
# rec(
#   exponent := ...,             # exponent of the group
#   size := ...,                 # group order
#   allorders := ...,            # list of all possible element orders in G
#   freqorders := ...,           # list of orders such that probabability
#                                # that a random el has one of these is ~ 1/2
#   probability := ...,          # probability that a random element has an
#                                # order in freqorders
#   notorders := ...,            # list of numbers that are *not* the order
#                                # of an element of G
# )
# the following components are optional:
#   exponent, allorders, notorders
# the following components are required:
#   freqorders, size, prob

RECOG.ElementOrderStats := function(pr,order,n,k)
  local col,i,j,ords,sums,pos;
  ords := EmptyPlist(n);
  for i in [1..n] do
      Add(ords,order(Next(pr)));
      for j in [1..k] do
          Next(pr);
      od;
      if i mod 100 = 0 then
          Print(QuoInt(i*100,n),"%\r");
      fi;
  od;
  Print("\n");
  col := Collected(ords);
  Sort(col,function(a,b) return a[2] > b[2]; end);
  sums := EmptyPlist(Length(col));
  sums[1] := col[1][2];
  for i in [2..Length(col)] do
      Add(sums,sums[i-1] + col[i][2]);
  od;
  pos := PositionSorted(sums,QuoInt(n,2));
  return rec(
             allorders     := Set(col, x -> x[1]),
             colorders     := col,
             exponent      := Lcm(ords),
             freqorders    := Set(col{[1..pos]}, x -> x[1]),
             independencek := k,
             probability   := sums[pos] / n,
             samplesize    := n,
            );
end;

RECOG.BinomialTab := [];

RECOG.InitBinomialTab := function()
    local i,j,s;
    for i in [1..100] do
        RECOG.BinomialTab[i] := EmptyPlist(i);
        Add(RECOG.BinomialTab[i],1);
        s := 0;
        for j in [1..i] do
            s := s + Binomial(i,j);
            Add(RECOG.BinomialTab[i],s);
        od;
    od;
end;
RECOG.InitBinomialTab();
Unbind(RECOG.InitBinomialTab);

RECOG.CheckFingerPrint := function(fp,orders)
    local count,i;
    if IsBound(fp.notorders) then
        if ForAny(orders,o->o in fp.notorders) then
            return 0;
        fi;
    fi;
    if IsBound(fp.exponent) then
        if ForAny(orders,o->fp.exponent mod o <> 0) then
            return 0;
        fi;
    elif IsBound(fp.size) then
        if ForAny(orders,o->fp.size mod o <> 0) then
            return 0;
        fi;
    fi;
    if IsBound(fp.allorders) then
        if ForAny(orders,o->not o in fp.allorders) then
            return 0;
        fi;
    fi;
    count := Number(orders,o->o in fp.freqorders);
    return RECOG.BinomialTab[Length(orders)][count+1]/2^(Length(orders));
end;

# Helper function to compute all primes up to a given integer via a prime sieve
RECOG.PrimesCache := ShallowCopy(Primes); # all primes < 1000
RECOG.PrimesCacheUpperBound := 1000;
RECOG.CachePrimesUpTo := function(n)
    local i, j, sieve;
    if RECOG.PrimesCacheUpperBound >= n then return; fi;
    sieve := BlistList([1..n], [1..n]);
    sieve[1] := false;
    for i in [2..Int(n/2)] do
        sieve[i*2] := false;
    od;
    i := 3;
    while i * i <= n do
        if sieve[i] then
            j := 3*i;
            while j <= n do
                sieve[j] := false;
                j := j + 2*i;
            od;
        fi;
        i := i + 2;
    od;
    RECOG.PrimesCache := ListBlist([1..n], sieve);
    RECOG.PrimesCacheUpperBound := n;
end;

