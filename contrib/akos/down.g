# finds first element of a list that is relative prime to all others
first:=function(list)
local i;

for i in [1..Length(list)] do
    if list[i]>1 and Gcd(list[i],Product(list)/list[i])=1 then
       return list[i];
    fi;
od;

return fail;
end;

# input: list=[SL(d,q), d, q] acting as a subgroup of some big SL(n,q)
# output: list=[SL(dd,q), dd, q] for some smaller dimensional subgroup
godown:=function(list)
local d,q,g,i, r, pol, factors, degrees, newdim, power, rr, ss;

g:=list[1];
d:=list[2];
q:=list[3];

Print(d,"\c");
#find an element with irreducible action of relative prime dimension to
#all other invariant subspaces
repeat
Print(".\c");
   r:=PseudoRandom(g);
   pol:=CharacteristicPolynomial(r);
   factors:=Factors(pol);
   degrees:=AsSortedList(List(factors,Degree));
   newdim:=first(degrees);
until newdim <> fail and newdim<=d/4;

# raise r to a power so that acting trivially outside one invariant subspace
degrees:=Filtered(degrees, x->x<>newdim);
power:=q^10*Lcm(List(degrees, x->q^x-1));
if q=2 then
   power:=power*2^10;
fi;
rr:=r^power;

#conjugate rr to hopefully get a smaller dimensional SL
ss:=rr^PseudoRandom(g);
return [Group(rr,ss),2*newdim,q];
end;

# input is a list=[group,dimension,q]
# output is a list=[SL(dd,q) subgroup, dd,q ]  dd in [4,6]
# for q=2,3,4 there is a significant chance for incorrect output!!!
constructsl46:=function(list)
local out, q;

out:=ShallowCopy(list);
q:=list[3];
repeat
   out:=godown(out);
until out[2] in [4,6];
return out;
end;
