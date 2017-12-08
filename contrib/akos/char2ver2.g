godownone:=function(g,subspg,q,d)
local n,y,yy,yyy,ready,order,es,null,subsph,z,x,a,b,c,h,r,divisors,cent,i,
pol,factors,degrees;

n:=DimensionOfMatrixGroup(g);
#d:=Dimension(subspg);
repeat
  ready:=false;
  y:=PseudoRandom(g);
  pol:=CharacteristicPolynomial(y);
  factors:=Factors(pol);
  degrees:=List(factors,Degree);
  if d-1 in degrees then
     order:=Order(y);
     yy:=y^(order/Gcd(order,q-1));
     if not IsOne(yy) then
          es:= Eigenspaces(GF(q),yy);
          es:=Filtered(es,x->Dimension(x)=d-1 and IsSubspace(subspg,x));
          if Length(es)>0 then
             subsph:=es[1];
             ready:=true;
          fi;
          yyy:=y^(Gcd(order,q-1));
     fi;
  fi;
until ready;

cent:=[yyy];
for i in [1..4] do
    z:=PseudoRandom(g);
    x:=yy^z;
    a := x;
    b := x^yy;
    c := x^(yy^2);
    h := Group(a,b,c);
    ready:=false;
    repeat
      r:=PseudoRandom(h);
      r:=r^(q*(q+1));
      if not IsOne(r) and r*yy=yy*r then
         Add(cent,yyy^r);
         ready:=true;
      fi;
    until ready=true;
od;
return [Group(cent), subsph];
end;

constructdata:=function(g,q)
local n,subgplist,subspg,i,j,r,hgens,output,h,workingdim,y,yy,order,
gens,degrees,factors,pol,ready,ready2,ready3,z;

n:=DimensionOfMatrixGroup(g);

if q-1>n then
  subspg:=VectorSpace(GF(q),One(g));
  subgplist:=[g,subspg];
  workingdim:=n;
  while workingdim > 2 do
    subgplist:=godownone(subgplist[1],subgplist[2],q,workingdim);
    workingdim:=workingdim-1;
  od;
else
  #case of small q
  n:=DimensionOfMatrixGroup(g);
  repeat
    ready:=false;
    y:=PseudoRandom(g);
    pol:=CharacteristicPolynomial(y);
    factors:=Factors(pol);
    degrees:=List(factors,Degree);
    if SortedList(degrees)=[1,1,n-2] then
       order:=Order(y);
       if order mod 2 = 0 then
          yy:=y^(order/2);
          ready:=true;
       fi;
    fi;
  until ready;

  ready2:=false;
  ready3:=false;
  repeat
     gens:=[yy];
     Add(gens,yy^PseudoRandom(g));
     Add(gens,yy^PseudoRandom(g));
     h:=Group(gens);
     for i in [1..10] do
       z:=PseudoRandom(h);
       pol:=CharacteristicPolynomial(z);
       factors:=Factors(pol);
       degrees:=List(factors,Degree);
       if Maximum(degrees)=2 then
          ready2:=true;
       elif Maximum(degrees)=3 then
          ready3:=true;
       fi;
       if ready2 and ready3 then
           break;
       fi;
     od;
     if not (ready2 and ready3) then
        ready2:=false;
        ready3:=false;
     fi;
  until ready2 and ready3;

  subgplist:=godownone(h,VectorSpace(GF(q),One(g)),q,3);
fi;

return subgplist;
end;

check:=function(out)
local basis,gens,x,vec;

basis:=Basis(out[2]);
gens:=GeneratorsOfGroup(out[1]);
for x in gens do
    for vec in basis do
        Print(vec*x in out[2]);
    od;
od;
return Size(out[1]);
end;
