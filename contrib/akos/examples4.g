#largest element orders until second semisimple

exceptionalscombined:=function(qlist)
local q, factors, output;

output:=[];
for q in qlist do
  factors:=FactorsInt(q);

  if Length(factors) mod 2 = 1 and factors[1]=2 and q>2 then
    Add(output, [ q+Sqrt(2*q)+1, q-1, ["2B2",q] ]);
  fi;

  if Length(factors) mod 2 = 1 and factors[1]=3 then
    if q=3 then
      Add(output, [9,7,["2G2",q] ]);
      Add(output, [7,3,["2G2",q] ]);
      Add(output, [7,2,["2G2",q] ]);
    else
      Add(output, [ q+Sqrt(3*q)+1, q-1, ["2G2",q] ]);
    fi;
  fi;

  if q=2 then
    Add(output, [ 12,8, ["G2",2] ]);
    Add(output, [ 12,7, ["G2",2] ]);
    Add(output, [ 8,7, ["G2",2] ]);
    Add(output, [ 7,6, ["G2",2] ]);
    Add(output, [ 7,4, ["G2",2] ]);
    Add(output, [ 7,3, ["G2",2] ]);
  elif IsPrime(q) then
    Add(output, [q^2+q+1, q^2+q, ["G2",q] ]);
    Add(output, [q^2+q+1, q^2, ["G2",q] ]);
    Add(output, [q^2+q+1, q^2-1, ["G2",q] ]);
  else
    Add(output, [q^2+q+1, q^2-1, ["G2",q] ]);
  fi;

  if q=2 then
    Add(output, [28,21, ["3D4",2] ]);
    Add(output, [21,18, ["3D4",2] ]);
    Add(output, [21,14, ["3D4",2] ]);
    Add(output, [21,13, ["3D4",2] ]);
  elif IsPrime(q) then
    Add(output, [(q^3-1)*(q+1), q*(q^3+1), ["3D4",q] ]);
    Add(output, [(q^3-1)*(q+1), q*(q^3-1), ["3D4",q] ]);
    Add(output, [(q^3-1)*(q+1), q^4-q^2+1, ["3D4",q] ]);
  else
    Add(output, [ (q^3-1)*(q+1), q^4-q^2+1, ["3D4",q] ]);
  fi;

  if q=2 then
    Add(output, [16,13, ["2F4",2] ]);
    Add(output, [13,12, ["2F4",2] ]);
    Add(output, [13,10, ["2F4",2] ]);
    Add(output, [13,8, ["2F4",2] ]);
    Add(output, [13,6, ["2F4",2] ]);
    Add(output, [13,5, ["2F4",2] ]);
  elif Length(factors) mod 2 = 1 and factors[1]=2 and q>2 then
    Add(output, [q^2+Sqrt(2*q^3)+q+Sqrt(2*q)+1, (q-1)*(q+Sqrt(2*q)+1),
       ["2F4",q] ]);
  fi;

  if q=2 then
    Add(output, [30,28, ["F4",2] ]);
    Add(output, [30,24, ["F4",2] ]);
    Add(output, [28,24, ["F4",2] ]);
    Add(output, [30,21, ["F4",2] ]);
    Add(output, [28,21, ["F4",2] ]);
    Add(output, [24,21, ["F4",2] ]);
    Add(output, [21,20, ["F4",2] ]);
    Add(output, [21,18, ["F4",2] ]);
    Add(output, [21,17, ["F4",2] ]);
  elif IsPrime(q) then
    Add(output, [q*(q+1)*(q^2+1), (q^3-1)*(q+1), ["F4",q] ]);
    Add(output, [(q^3-1)*(q+1), q^4+q, ["F4",q] ]);
    Add(output, [(q^3-1)*(q+1), q^4+1, ["F4",q] ]);
    if q=3 then
      Add(output, [104,90, ["F4",q] ]);
    fi;
  else
    Add(output, [(q^3-1)*(q+1), q^4+1, ["F4",q] ]);
  fi;

  if IsPrime(q) then # works also for q=2
    Add(output, [q*(q^6-1)/((q-1)*Gcd(3,q-1)),(q+1)*(q^5-1)/Gcd(3,q-1),
                 ["E6",q] ]);
    Add(output, [ (q+1)*(q^5-1)/Gcd(3,q-1), (q^2+q+1)*(q^4-q^2+1)/Gcd(3,q-1),
                ["E6",q] ]);
  else
    Add(output, [ (q+1)*(q^5-1)/Gcd(3,q-1), (q^2+q+1)*(q^4-q^2+1)/Gcd(3,q-1),
                ["E6",q] ]);
  fi;

  if q=2 then
    Add(output, [35,33, ["2E6",2] ]);
  elif IsPrime(q) then
    Add(output, [(q+1)*(q^2+1)*(q^3-1)/Gcd(3,q+1),
                  q*(q^5+1)/Gcd(3,q+1), ["2E6",q] ]);
    Add(output, [(q+1)*(q^2+1)*(q^3-1)/Gcd(3,q+1),
                  (q^6-1)/Gcd(3,q+1), ["2E6",q] ]);
  else
    Add(output, [(q+1)*(q^2+1)*(q^3-1)/Gcd(3,q+1),
                  (q^6-1)/Gcd(3,q+1), ["2E6",q] ]);
  fi;

  if q=2 then
    Add(output, [255,252, ["E7",q] ]);
    Add(output, [255,217, ["E7",q] ]);
  elif IsPrime(q) and q mod 4 = 1 then
    Add(output, [(q^2+q+1)*(q^5-1)/Gcd(2,q-1),
                  q*(q+1)*(q^2+1)*(q^3-1)/Gcd(2,q-1), ["E7",q] ]);
    Add(output, [(q^2+q+1)*(q^5-1)/Gcd(2,q-1),
                 (q+1)*(q^6-q^3+1)/Gcd(2,q-1), ["E7",q] ]);
  elif q mod 4 = 1 then # q composite
    Add(output, [(q^2+q+1)*(q^5-1)/Gcd(2,q-1),
                 (q+1)*(q^6-q^3+1)/Gcd(2,q-1), ["E7",q] ]);
  else # q mod 4 = 0,3 prime and composite alike
    Add(output, [(q+1)*(q^2+1)*(q^4+1)/Gcd(2,q-1),
                 (q^2+q+1)*(q^5-1)/Gcd(2,q-1), ["E7",q] ]);
  fi;

  if q mod 3 = 1 then
    if IsPrime(q) and q mod 4 = 3 then
      Add(output, [(q+1)*(q^2+q+1)*(q^5-1), q*(q+1)*(q^2+1)*(q^4+1),
        ["E8",q] ]);
      Add(output, [(q+1)*(q^2+q+1)*(q^5-1), (q+1)*(q^2+1)*(q^5-1),
        ["E8",q] ]);
    else
      Add(output, [(q+1)*(q^2+q+1)*(q^5-1), (q+1)*(q^2+1)*(q^5-1),
        ["E8",q] ]);
    fi;
  else
    Add(output, [(q+1)*(q^2+q+1)*(q^5-1), (q^2+q+1)*(q^6+q^3+1),
        ["E8",q] ]);
  fi;
od;

return output;
end;

##########################################################################
# start classical groups

#largest non-semisimples: m1,m2, m1',m2',q*m1'(PSp(d-2)), q*m2'(PSP(d-2))
#for q=3, also 3^(d/2)-3, 3^(d/2)-9, 9*m1'(PSp(d-4)), 9*m2'(PSp(d-4))
pspcombined:=function(d,q)
local k,r;

if d=4 then
  if q=3 then
     return [ 12, 9, 6, 5, 4 ];
  else
     return [q^2+q, q^2-q, q*(q+1)/2, (q^2+1)/2, (q^2-1)/2];
  fi;
fi;

if d=6 then
  if q=3 then
     return  [ 36, 30, 24, 20, 18, 15, 14 ];
  else
     return [q^3+q, q^3-q, (q+1)*(q^2+1)/2, q*(q^2+1)/2, (q^3+1)/2];
  fi;
fi;

if d=8 then
  if q=3 then
     return  [ 90, 84, 78, 72, 60, 52, 45, 42, 41 ];
  else
     return [q^4+q, q^4-q, q*(q+1)*(q^2+1)/2, (q+1)*(q^3-1)/2,
       (q^4+q)/2, (q^4+1)/2];
  fi;
fi;

if d>=10 then
  k:=QuotientRemainder(d,8)[1];
  r:=QuotientRemainder(d,8)[2];
  if r=0 then
    if q=3 then
      return [3^(4*k)+9, 3^(4*k)+3, 3^(4*k)-3, 3^(4*k)-9,
       3*(3+1)*(3^(4*k-2)+1)/2, (3+1)*(3^(4*k-1)-1)/2, 9*(3+1)*(3^(4*k-3)-1)/2,
  9*(3^2+1)*(3^(4*k-4)+1)/2,3*(3^2+1)*(3^(4*k-3)+1)/2,(3^2+1)*(3^(4*k-2)-1)/2];
    else
      return [q^(4*k)+q, q^(4*k)-q,
              q*(q+1)*(q^(4*k-2)+1)/2, (q+1)*(q^(4*k-1)-1)/2,
              q*(q^2+1)*(q^(4*k-3)+1)/2, (q^2+1)*(q^(4*k-2)-1)/2];
    fi;
  fi;
  if r=2 then
    if q=3 and d=10 then
      return [ 252, 246, 240, 234, 180, 164, 156, 140 ];
    elif q=3 and d>10 then
      return [3^(4*k+1)+9, 3^(4*k+1)+3, 3^(4*k+1)-3, 3^(4*k+1)-9,
        9*(3+1)*(3^(4*k-2)+1)/2, (3+1)*(3^(4*k)+1)/2, 3*(3+1)*(3^(4*k-1)-1)/2,
     9*(3^2+1)*(3^(4*k-3)+1)/2,(3^2+1)*(3^(4*k-1)+1)/2];
    else
      return [q^(4*k+1)+q, q^(4*k+1)-q,
              (q+1)*(q^(4*k)+1)/2, q*(q+1)*(q^(4*k-1)-1)/2,
              (q^2+1)*(q^(4*k-1)+1)/2];
    fi;
  fi;
  if r=4 then
    if q=3 then
      return [3^(4*k+2)+9, 3^(4*k+2)+3, 3^(4*k+2)-3, 3^(4*k+2)-9,
       3*(3+1)*(3^(4*k)+1)/2, (3+1)*(3^(4*k+1)-1)/2, 9*(3+1)*(3^(4*k-1)-1)/2,
       3*(3^2+1)*(3^(4*k-1)+1)/2,(3^2+1)*(3^(4*k)+1)/2];
    else
      return [q^(4*k+2)+q, q^(4*k+2)-q,
              q*(q+1)*(q^(4*k)+1)/2, (q+1)*(q^(4*k+1)-1)/2,
              q*(q^2+1)*(q^(4*k-1)+1)/2, (q^2+1)*(q^(4*k)+1)/2];
    fi;
  fi;
  if r=6 then
    if q=3 then
      return [3^(4*k+3)+9, 3^(4*k+3)+3, 3^(4*k+3)-3, 3^(4*k+3)-9,
       9*(3+1)*(3^(4*k)+1)/2, (3+1)*(3^(4*k+2)+1)/2, 3*(3+1)*(3^(4*k+1)-1)/2,
  9*(3^2+1)*(3^(4*k-1)+1)/2,3*(3^2+1)*(3^(4*k)+1)/2,(3^2+1)*(3^(4*k+1)+1)/2];
    else
      return [q^(4*k+3)+q, q^(4*k+3)-q,
              (q+1)*(q^(4*k+2)+1)/2, q*(q+1)*(q^(4*k+1)-1)/2,
              q*(q^2+1)*(q^(4*k)+1)/2, (q^2+1)*(q^(4*k+1)+1)/2];
    fi;
  fi;
fi;

end;

#largest non-semisimples: m1, m2, m1',m2', q*m1'(PSp(d-3)), q*m2'(PSP(d-3))
#there are coincidences among these!!
#for q=3, also 9*m1'(PSp(d-5)), 9*m2'(PSp(d-5))
#for all values of k: just delete the first four from pspcombined(d-1,q)
#if q=3; delete the first two from pspcombined(d-1,q) if q>3
ocombined:=function(d,q)
local k,r;

if d=7 then
  if q=3 then
     return  [ 20, 18, 15, 14 ];
  else
     return [(q+1)*(q^2+1)/2, q*(q^2+1)/2, (q^3+1)/2];
  fi;
fi;

if d=9 then
  if q=3 then
     return  [ 60, 52, 45, 42, 41 ];
  else
     return [q*(q+1)*(q^2+1)/2, (q+1)*(q^3-1)/2,
       (q^4+q)/2, (q^4+1)/2];
  fi;
fi;

if d>=10 then
  k:=QuotientRemainder(d,8)[1];
  r:=QuotientRemainder(d,8)[2];
  if r=1 then
    if q=3 then
      return [
       3*(3+1)*(3^(4*k-2)+1)/2, (3+1)*(3^(4*k-1)-1)/2, 9*(3+1)*(3^(4*k-3)-1)/2,
  9*(3^2+1)*(3^(4*k-4)+1)/2,3*(3^2+1)*(3^(4*k-3)+1)/2,(3^2+1)*(3^(4*k-2)-1)/2];
    else
      return [
              q*(q+1)*(q^(4*k-2)+1)/2, (q+1)*(q^(4*k-1)-1)/2,
              q*(q^2+1)*(q^(4*k-3)+1)/2, (q^2+1)*(q^(4*k-2)-1)/2];
    fi;
  fi;
  if r=3 then
    if q=3 and d=11 then
      return [ 180, 164, 156, 140 ];
    elif q=3 and d>11 then
      return [
        9*(3+1)*(3^(4*k-2)+1)/2, (3+1)*(3^(4*k)+1)/2, 3*(3+1)*(3^(4*k-1)-1)/2,
     9*(3^2+1)*(3^(4*k-3)+1)/2,(3^2+1)*(3^(4*k-1)+1)/2];
    else
      return [
              (q+1)*(q^(4*k)+1)/2, q*(q+1)*(q^(4*k-1)-1)/2,
              (q^2+1)*(q^(4*k-1)+1)/2];
    fi;
  fi;
  if r=5 then
    if q=3 then
      return [
       3*(3+1)*(3^(4*k)+1)/2, (3+1)*(3^(4*k+1)-1)/2, 9*(3+1)*(3^(4*k-1)-1)/2,
       3*(3^2+1)*(3^(4*k-1)+1)/2,(3^2+1)*(3^(4*k)+1)/2];
    else
      return [
              q*(q+1)*(q^(4*k)+1)/2, (q+1)*(q^(4*k+1)-1)/2,
              q*(q^2+1)*(q^(4*k-1)+1)/2, (q^2+1)*(q^(4*k)+1)/2];
    fi;
  fi;
  if r=7 then
    if q=3 then
      return [
       9*(3+1)*(3^(4*k)+1)/2, (3+1)*(3^(4*k+2)+1)/2, 3*(3+1)*(3^(4*k+1)-1)/2,
  9*(3^2+1)*(3^(4*k-1)+1)/2,3*(3^2+1)*(3^(4*k)+1)/2,(3^2+1)*(3^(4*k+1)+1)/2];
    else
      return [
              (q+1)*(q^(4*k+2)+1)/2, q*(q+1)*(q^(4*k+1)-1)/2,
              q*(q^2+1)*(q^(4*k)+1)/2, (q^2+1)*(q^(4*k+1)+1)/2];
    fi;
  fi;
fi;

end;


opluscombined:=function(d,q)
local k,r;

if d=8 then
  if q=3 then
    return [ 20,18,15,14 ];
  else
    return [ (q^4-1)/4, (q^4-1)/8 ];
  fi;
fi;

if d=12 then
  return [ (q+1)*(q^2+1)*(q^3-1)/4, (q^2+1)*(q^4+1)/4 ];
fi;

if d in [10,14,18] then
  k:=d/2;
  return [ (q+1)*(q^(k-1)+1)/Gcd(q-1,4), q*(q+1)*(q^(k-2)-1)/Gcd(q-1,4),
            (q^2+1)*(q^(k-2)+1)/Gcd(q-1,4) ];
fi;

if d=16 then
  return [ q*(q+1)*(q^2+1)*(q^4+1)/4, (q+1)*(q^2+1)*(q^5-1)/4,
          (q+1)*(q^4+1)*(q^3-1)/4 ];
fi;

if d>=20 then
  k:=QuotientRemainder(d,16)[1];
  r:=QuotientRemainder(d,16)[2];
  if r=4 then
    return [ (q+1)*(q^2+1)*(q^(8*k-1)-1)/4, (q+1)*(q^4+1)*(q^(8*k-3)-1)/4 ];
  fi;
  if r=12 then
    return [ (q+1)*(q^2+1)*(q^(8*k+3)-1)/4, q*(q+1)*(q^4+1)*(q^(8*k)+1)/4,
             (q+1)*(q^4+1)*(q^(8*k+1)-1)/4 ];
  fi;
  if r in [2,6,10,14] then
    k:=(d-2)/2;
    if q mod 4 =1 then
      return [ (q+1)*(q^k+1)/4, q*(q+1)*(q^(k-1)-1)/4,
               (q^2+1)*(q^4+1)*(q^(k-5)-1)/4 ];
    else
      return [ (q+1)*(q^k+1)/2, q*(q+1)*(q^(k-1)-1)/2, (q^2+1)*(q^(k-1)+1)/2 ];
    fi;
  fi;
  if r in [0,8] then
    k:=d/2;
    return [ q*(q+1)*(q^2+1)*(q^(k-4)+1)/4, (q+1)*(q^2+1)*(q^(k-3)-1)/4,
             q*(q+1)*(q^4+1)*(q^(k-6)+1)/4,(q+1)*(q^4+1)*(q^(k-5)-1)/4 ];
  fi;
fi;

end;

ominuscombined:=function(d,q)
local factors,a,e,list,k,r;

if d mod 4 = 0 then
  k:=d/4;
  list:=[ q*(q+1)*(q^(2*k-2)+1)/2, (q+1)*(q^(2*k-1)-1)/2 ];
  if k in [2,3] then
    Add(list, (q^(2*k)+1)/2);
  elif k mod 2 = 0 then #k>3 even
    Add(list, (q^2+1)*(q^(2*k-2)-1)/2);
  else #k>3 odd
    Add(list, (q^3+1)*(q^(2*k-3)-1)/2);
  fi;
  return list;
fi;

if d=10 then
  if q=3 then
    return [ 84, 80, 65 ];
  else
    return [ (q^2+1)*(q^3-1)/Gcd(4,q+1), (q^5+1)/Gcd(4,q+1) ];
  fi;
fi;

if d=14 then
  if q mod 4 = 1 then
    return [(q^2+1)*(q^5-1)/2, (q^7+1)/2 ];
  elif q=3 then
    return [ 820, 780, 732, 728 ];
  else # q mod 4 =3 and q>3
    return [ (q+1)*(q^2+1)*(q^4+1)/4, q*(q+1)*(q^2+1)*(q^3-1)/4,
              (q^2+1)*(q^5-1)/4 ];
  fi;
fi;

if d >= 18 and d mod 4 = 2 and q mod 4 = 1 then
  k := Int(d/4);
  return [ (q^2+1)*(q^(2*k-1)-1)/2, (q^4+1)*(q^(2*k-3)-1)/2 ];
fi;

if d=18 and q=3 then
  return [ 7260, 6564, 6560, 6396, 6292 ];
fi;

if d=18 and q>3 and q mod 4 = 3 then
  return [ q*(q+1)*(q^2+1)*(q^5-1)/4, q*(q+1)*(q^4+1)*(q^3-1)/4,
           (q^2+1)*(q^3+1)*(q^4+1)/4, (q^2+1)*(q^7-1)/4 ];
fi;

if d >= 22 and d mod 8 = 6 and q mod 4 = 3 then
  k := Int(d/8);
  return [ (q+1)*(q^2+1)*(q^(4*k)+1)/4, q*(q+1)*(q^2+1)*(q^(4*k-1)-1)/4,
            (q+1)*(q^4+1)*(q^(4*k-2)+1)/4 ];
fi;

if d=26 and q mod 4 =3 then
  list := [ q*(q+1)*(q^2+1)*(q^9-1)/4, (q+1)*(q^4+1)*(q^8+1)/4,
           q*(q+1)*(q^4+1)*(q^7-1)/4 ];
  if q=3 then
    Add(list, q*(q+1)*(q^11+1)/4);
    Add(list, (q+1)*(q^12-1)/4);
  else
    Add(list, q*(q+1)*(q^6+1)*(q^5-1)/4);
    Add(list, q*(q+1)*(q^8+1)*(q^3-1)/4);
    Add(list, (q^2+1)*(q^3+1)*(q^8+1)/4);
  fi;
  return list;
fi;


if d > 26 and d mod 16 = 10 and q mod 4 = 3 then
  k := Int(d/16);
  return [ q*(q+1)*(q^2+1)*(q^(8*k+1)-1)/4, (q+1)*(q^4+1)*(q^(8*k)+1)/4,
           q*(q+1)*(q^4+1)*(q^(8*k-1)-1)/4, q*(q+1)*(q^6+1)*(q^(8*k-3)-1)/4,
           (q+1)*(q^8+1)*(q^(8*k-4)+1)/4 ];
fi;

if d>18 and d mod 16 = 2 and q mod 4 = 3 then
  factors:=Factors(d-2);
  if factors[Length(factors)] = 2 then
    e := Length(factors);
    if q=3 then
      list:= [ 3*(3^(2^(e-1)-1)+1), 3^(2^(e-1))-1,
               (3^(2^(e-2)-1)-1)*(3^(2^(e-2)+1)-1) ];
      for r in [1..2^(e-3)] do
        Add(list, 3*(3^(2*r)+1)*(3^(2^(e-1)-1-2*r)-1) );
      od;
      list := reverse(Set(list));
      return list;
    else
      list:= [ (q^2+1)*(q^3+1)*(q^(2^(e-1)-4)+1)/4,
               (q^2+1)*(q^4+1)*(q^(2^(e-1)-5)+1)/4 ];
      for r in [1..2^(e-2)-2] do
        Add(list, q*(q+1)*(q^(2*r)+1)*(q^(2^(e-1)-1-2*r)-1)/4 );
      od;
      list := reverse(Set(list));
      return list;
    fi;
  elif factors[Length(factors)] = 3 and factors[Length(factors)-1] = 2 then
    e := Length(factors)-1;
    if q=3 then
      list:= [ 3*(3^(3*2^(e-1)-1)+1), 3^(3*2^(e-1))-1,
               (3^(2^e)+1)*(3^(2^(e-1))+1) ];
      for r in [1..3*2^(e-3)-1] do
        Add(list, 3*(3^(2*r)+1)*(3^(3*2^(e-1)-1-2*r)-1) );
      od;
      list := reverse(Set(list));
      return list;
    else
      list:= [ (q^2+1)*(q^3+1)*(q^(3*2^(e-1)-4)+1)/4,
               (q+1)*(q^(2^e)+1)*(q^(2^(e-1))+1)/4 ];
      for r in [1..3*2^(e-2)-2] do
        Add(list, q*(q+1)*(q^(2*r)+1)*(q^(3*2^(e-1)-1-2*r)-1)/4 );
      od;
      list := reverse(Set(list));
      return list;
    fi;
  else
    e:=Maximum(Filtered([1..Length(factors)],x->factors[x]=2));
    a:=(d-2)/(2^e);
    list:= [ (q+1)*(q^(2^(e-1))+1)*(q^((a-1)*2^(e-1))+1)/4,
             (q+1)*(q^(2*2^(e-1))+1)*(q^((a-2)*2^(e-1))+1)/4 ];
      for r in [1..2^(e-1)-1] do
        Add(list, q*(q+1)*(q^(2*r)+1)*(q^(a*2^(e-1)-1-2*r)-1)/4 );
      od;
      list := reverse(Set(list));
      return list;
  fi;  # largest prime factor of d-2
fi;

end;

a:=function(d);
  return First([2..2*d],x->((Gcd(x,d-x)=1) and (x mod 2 = 1)));
end;


pslcombined:=function(d,q);

if d=2 then
  return [q, (q+1)/2, (q-1)/2];
elif d=3 and q=2 then
  return [7,4,3];
else
  return pslexpected([d],[q])[d][q];
fi;

end;


psucombined:=function(d,q)
local k,list,delta,i,count,list2;

    delta:=(q+1)*Gcd(q+1,d);
    if d mod 2 = 1 then
      k := Int(d/2);
      list:=[ (q^(d-2)+1)*q*(q+1)/delta, (q^(d-1)-1)*(q+1)/delta ];
      if k in [1,2,4] then
        Add(list, (q^d+1)/delta);
        return list;
      else
        Add(list, (q^a(d)+1)*(q^(d-a(d))-1)/delta);
        return list;
      fi;
    fi;

    if d=4 and q=3 then
      return [12, 9, 8, 7];
    fi;
    if d=6 and q=5 then
      return [ 630, 624, 521 ];
    fi;
    if d mod 2 = 0 and d mod (q+1) = 0 and not([d,q] in [[4,3],[6,5]]) then
      list:=[q^(d-2)+q, q^(d-2)-1, (q^a(d-1)+1)*(q^(d-1-a(d-1))-1)/(q+1)];
      for i in [3..d-4] do
        if Gcd(i,d-2-i)=1 and i mod 2 = 1 then
          Add(list, q*(q^i+1)*(q^(d-2-i)+1)/(q+1));
        fi;
      od;
      list:=reverse(Set(list));
      count:=0;
      i:=0;
      list2:=[];
      repeat
        i:=i+1;
        Add(list2,list[i]);
        if list[i] mod q > 0 then
          count:=count+1;
        fi;
      until count=2;
      return list2;
    fi;
    if d mod 2 = 0 and d mod (q+1) > 0 then
      k:=d/2;
      list:=[ (q^(d-1)+1)*(q+1)/delta, (q^(d-2)-1)*q*(q+1)/delta];
      if k in [2,3] then
        Add(list, (q^d-1)/delta);
        return list;
      else
        Add(list, (q^(d-a(d))+1)*(q^a(d)+1)/delta);
        return list;
      fi;
    fi;

end;

finalcheck:=function(psu)
local d,q,bad;

bad:=[];

for d in [1..Length(psu)] do
  if IsBound(psu[d]) then
    for q in [1..Length(psu[d])] do
      if IsBound(psu[d][q]) then
        if psu[d][q]<>psucombined(d,q) then
          Add(bad,[d,q]);
        fi;
      fi;
    od;
  fi;
od;

return bad;

end;

process:=function(list,q)
local relprimes,pairs,i,j,pos1,pos2;

pairs:=[];

relprimes:=Filtered(list,x-> Gcd(x,q)=1);
pos1:=Position(list,relprimes[1]);
pos2:=Position(list,relprimes[2]);
if pos2<Length(list) then Error(); fi;
for i in [1..pos1-1] do
  for j in [i+1..pos1] do
    Add(pairs, [list[i],list[j]]);
  od;
od;
for i in [pos1+1..pos2] do
  Add(pairs, [list[pos1],list[i]]);
od;

return pairs;

end;

constructmixeddata:=function(primes,dim)
local output, list, data, d, pair, pairs, q, i, bad, reallybad;

data:=[];
for d in [2..dim] do for q in primes do
  if IsPrime(q) then
    if (d=2 and q>3) or d>2 then
      Add(data, [ pslcombined(d,q), ["l",d,q] ]);
    fi;
  else
     Add(data,[ [pslexpected([d],[q])[d][q][1],
            pslexpected([d],[q])[d][q][2] ], ["l",d,q] ]);
  fi;
od;od;

for d in [3..dim] do for q in primes do
  if IsPrime(q) then
    if [d,q]<>[3,2] then
      Add(data, [ psucombined(d,q), ["u",d,q] ]);
    fi;
  else
    Add(data,[ [ psuexpected([d],[q])[d][q][1],
            psuexpected([d],[q])[d][q][2] ], ["u",d,q] ]);
  fi;
od;od;

for d in List([2..Int(dim/2)],x->2*x) do for q in primes do
 if (q mod 2 = 1) or (d <=36) then
  if IsPrime(q) then
    Add(data, [ pspcombined(d,q), ["s",d,q] ]);
  else
    Add(data,[ [ pspexpected([d],[q])[d][q][1],
            pspexpected([d],[q])[d][q][2] ], ["s",d,q] ]);
  fi;
 fi;
od;od;

for d in List([3..Int(dim/2)],x->2*x+1) do for q in primes do
 if (q mod 2 = 1) then
  if IsPrime(q) then
    Add(data, [ ocombined(d,q), ["o",d,q] ]);
  else
    Add(data,[ [pomegaexpected([d],[q])[d][q][1],
            pomegaexpected([d],[q])[d][q][2] ], ["o",d,q] ]);
  fi;\
 fi;
od;od;

for d in List([4..Int(dim)],x->2*x) do for q in primes do
 if (q mod 2 = 1) or (d <=36) then
  if IsPrime(q) then
    Add(data, [ opluscombined(d,q), ["o+",d,q] ]);
  else
    Add(data,[ [pomegaplusexpected([d],[q])[d][q][1],
            pomegaplusexpected([d],[q])[d][q][2] ], ["o+",d,q] ]);
  fi;
 fi;
od;od;

for d in List([4..Int(dim)],x->2*x) do for q in primes do
 if (q mod 2 = 1) or (d <=36) then
  if IsPrime(q) then
    Add(data, [ ominuscombined(d,q), ["o-",d,q] ]);
  else
    Add(data,[ [pomegaminusexpected([d],[q])[d][q][1],
            pomegaminusexpected([d],[q])[d][q][2] ], ["o-",d,q] ]);
  fi;
 fi;
od;od;

output:=[];
for list in data do
  pairs:=process(list[1],list[2][3]);
  for pair in pairs do
    Add(output, [ pair[1],pair[2],list[2] ]);
  od;
od;

Append(output, exceptionalscombined(primes));

output:=Set(output);
bad:=[];
for i in [1..Length(output)-1] do
  if output[i][1]=output[i+1][1] and output[i][2]=output[i+1][2] then
    Add(bad, Concatenation(output[i], [output[i+1][3]]));
  fi;
od;

reallybad:=Filtered(bad, x->(not IsInt(x[3][Length(x[3])])) or
                            (not IsInt(x[4][Length(x[4])])) or
                            (FactorsInt(x[3][Length(x[3])])[1]<>
                            FactorsInt(x[4][Length(x[4])])[1]));

return [output,bad,reallybad];

end;

#list of groups having cross-characteristic representations of dimension
#at most dimbound
grouplist:=function(dimbound)
local list, q, n;

list:=[];
for q in [4..2*dimbound] do
  if IsPrimePowerInt(q) then
    Add(list, ["l",2,q]);
  fi;
od;

for n in [3..LogInt(dimbound,2)] do
  for q in [2..RootInt(dimbound,2)] do
    if IsPrimePowerInt(q) and (q^n-q)/(q-1)-1 <= dimbound then
      Add(list, ["l",n,q]);
    fi;
  od;
od;

for n in [2..LogInt(dimbound,2)] do
  for q in [2..RootInt(dimbound,2)] do
    if IsPrimePowerInt(q) and (q mod 2 = 1) and (q^n-1)/2 <= dimbound then
      Add(list, ["s",2*n,q]);
    fi;
    if IsPrimePowerInt(q) and (q mod 2 = 0) and
        (q^n-1)*(q^n-q)/(2*(q+1)) <= dimbound then
      Add(list, ["s",2*n,q]);
    fi;
  od;
od;

for n in [3..LogInt(dimbound,2)] do
  for q in [2..RootInt(dimbound,2)] do
    if IsPrimePowerInt(q) and  (q^n-1)/(q+1) <= dimbound and
         [n,q]<>[3,2] then
      Add(list, ["u",n,q]);
    fi;
  od;
od;

for n in [4..LogInt(dimbound,2)] do
  if (2^n-1)*(2^(n-1)-1)/3 <= dimbound then
    Add(list, ["o+",2*n,2]);
  fi;
  if (3^n-1)*(3^(n-1)-1)/8 <= dimbound then
    Add(list, ["o+",2*n,3]);
  fi;
  for q in [4..RootInt(dimbound,2)] do
    if IsPrimePowerInt(q) and (q^n-1)*(q^(n-1)+q)/(q^2-1) <= dimbound then
      Add(list, ["o+",2*n,q]);
    fi;
  od;
od;

for n in [4..LogInt(dimbound,2)] do
  for q in [2..RootInt(dimbound,2)] do
    if IsPrimePowerInt(q) and (q^n+1)*(q^(n-1)-q)/(q^2-1)-1 <= dimbound then
      Add(list, ["o-",2*n,q]);
    fi;
  od;
od;

for n in [3..LogInt(dimbound,2)] do
  if (3^n-1)*(3^n-3)/8 <= dimbound then
    Add(list, ["o",2*n+1,3]);
  fi;
  for q in [5..RootInt(dimbound,2)] do
    if IsPrimePowerInt(q) and (q mod 2 = 1) and
        (q^(2*n)-1)/(q^2-1)-2 <= dimbound then
      Add(list, ["o",2*n+1,q]);
    fi;
  od;
od;

for n in [2..LogInt(dimbound,2)] do
  if (n mod 2 = 1) and (2^n-1)*RootInt(2^n/2) <= dimbound then
    Add(list, ["2B2",2^n]);
  fi;
od;

for n in [2..LogInt(dimbound,2)] do
  if (n mod 2 = 1) and (3^n-1)*3^n <= dimbound then
    Add(list, ["2G2",3^n]);
  fi;
od;

for q in [3..RootInt(dimbound,2)] do
  if IsPrimePowerInt(q) and (q mod 3 <> 0) and q^3-1 <= dimbound then
    Add(list, ["G2",q]);
  fi;
  if IsPrimePowerInt(q) and (q mod 3 = 0) and q^4+q^2 <= dimbound then
    Add(list, ["G2",q]);
  fi;
od;

for q in [2..RootInt(dimbound,2)] do
  if IsPrimePowerInt(q) and q^5-q^3+q-1 <= dimbound then
    Add(list, ["3D4",q]);
  fi;
od;

for n in [1..LogInt(dimbound,2)] do
  if (n mod 2 = 1) and (2^(5*n)-2^(4*n))*RootInt(2^n/2) <= dimbound then
    Add(list, ["2F4",2^n]);
  fi;
od;

for q in [2..RootInt(dimbound,2)] do
  if IsPrimePowerInt(q) and (q mod 2 = 1) and q^8+q^4-2 <= dimbound then
    Add(list, ["F4",q]);
  fi;
  if IsPrimePowerInt(q) and (q mod 2 = 0) and
     (q^3-1)*(q^8-q^7)/2 <= dimbound then
    Add(list, ["F4",q]);
  fi;
od;

for q in [2..RootInt(dimbound,2)] do
  if IsPrimePowerInt(q) and q^11-q^9 <= dimbound then
    Add(list, ["2E6",q]);
    Add(list, ["E6",q]);
  fi;
  if IsPrimePowerInt(q) and q^17-q^15 <= dimbound then
    Add(list, ["E7",q]);
  fi;
  if IsPrimePowerInt(q) and q^29-q^27 <= dimbound then
    Add(list, ["E8",q]);
  fi;
od;

return list;

end;
