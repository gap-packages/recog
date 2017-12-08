expected:=function(qlist)
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
    else
      Add(output, [ q+Sqrt(3*q)+1, q-1, ["2G2",q] ]);
    fi;
  fi;

  if q=2 then
    Add(output, [ 12,8, ["G2",2] ]);
  elif IsPrime(q) then
    Add(output, [q^2+q+1, q^2+q, ["G2",q] ]);
  else
    Add(output, [q^2+q+1, q^2-1, ["G2",q] ]);
  fi;

  if q=2 then
    Add(output, [28,21, ["3D4",2] ]);
  elif IsPrime(q) then
    Add(output, [(q^3-1)*(q+1), q*(q^3+1), ["3D4",q] ]);
  else
    Add(output, [ (q^3-1)*(q+1), q^4-q^2+1, ["3D4",q] ]);
  fi;

  if q=2 then
    Add(output, [16,13, ["2F4",2] ]);
  elif Length(factors) mod 2 = 1 and factors[1]=2 and q>2 then
    Add(output, [q^2+Sqrt(2*q^3)+q+Sqrt(2*q)+1, (q-1)*(q+Sqrt(2*q)+1),
       ["2F4",q] ]);
  fi;

  if q=2 then
    Add(output, [40,32, ["F4",2] ]);
  elif IsPrime(q) then
    Add(output, [q*(q+1)*(q^2+1), (q^3-1)*(q+1), ["F4",q] ]);
  else
    Add(output, [(q^3-1)*(q+1), q^4+1, ["F4",q] ]);
  fi;

  if IsPrime(q) then # works also for q=2
    Add(output, [q*(q^6-1)/((q-1)*Gcd(3,q-1)),(q+1)*(q^5-1)/Gcd(3,q-1),
                 ["E6",q] ]);
  else
    Add(output, [ (q+1)*(q^5-1)/Gcd(3,q-1), (q^2+q+1)*(q^4-q^2+1)/Gcd(3,q-1),
                ["E6",q] ]);
  fi;

  if IsPrime(q) then # works also for q=2
    Add(output, [(q+1)*(q^2+1)*(q^3-1)/Gcd(3,q+1),
                  q*(q^5+1)/Gcd(3,q+1), ["2E6",q] ]);
  else
    Add(output, [(q+1)*(q^2+1)*(q^3-1)/Gcd(3,q+1),
                  (q^6-1)/Gcd(3,q+1), ["2E6",q] ]);
  fi;

  if q=2 then
    Add(output, [255,252, ["E7",q] ]);
  elif IsPrime(q) and q mod 4 = 1 then
    Add(output, [(q^2+q+1)*(q^5-1)/Gcd(2,q-1),
                  q*(q+1)*(q^2+1)*(q^3-1)/Gcd(2,q-1), ["E7",q] ]);
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

expectedspor:= [
[ 11,8,["M11"] ],
[ 11,8,["M22"] ],
[ 11,10,["M12"] ],
[ 15,12,["J2"] ],
[ 19,15,["J1"] ],
[ 19,17,["J3"] ],
[ 20,15,["HS"] ],
[ 23,15,["M23"] ],
[ 23,21,["M24"] ],
[ 24,21,["Suz"] ],
[ 28,21,["He"] ],
[ 29,26,["Ru"] ],
[ 30,15,["McL"] ],
[ 30,24,["Co3"] ],
[ 30,24,["Fi22"] ],
[ 30,28,["Co2"] ],
[ 31,28,["O'N"] ],
[ 39,36,["Th"] ],
[ 40,35,["HN"] ],
[ 60,42,["Co1"] ],
[ 60,42,["Fi23"] ],
[ 66,44,["J4"] ],
[ 60,45,["Fi24'"] ],   # changed by Max to Fi24' from Fi24
[ 67,42,["Ly"] ],
[ 70,66,["B"] ],
[ 119,110,["M"] ] ];
