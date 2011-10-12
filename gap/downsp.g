#for symplectic groups
#Version 1.2

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

# finds first element of a list such that half of the number is 
# relative prime to all others
# special treatment for 2
firsthalf:=function(list)
local i, bad;
#Print(list,"\n");
for i in [1..Length(list)] do 
    if list[i]>2 and list[i] mod 2 = 0 and 
       Gcd(list[i]/2,Product(list)/list[i])=1 then
       return list[i];
    elif list[i]=2 then 
       #at first occurrence of 2 on list, check that the next one is not 2
       if i<Length(list) and list[i+1]=2 then 
          break;
       fi;
       #good case: later numbers are odd or multiples of 4
       #multiples of 4 must occur with multiplicity 1
       #get rid of odd numbers, they are OK
       bad:=Filtered(list{[i+1..Length(list)]},x->x mod 2 =0);
       if ForAny(bad,x-> x mod 4 =2) then
          #any odd multiple of 2 eliminates taking 2
          continue;
       elif Length(Set(bad)) < Length(bad) then
          #large multiplicities eliminate taking  2
          continue;
       else
          return list[i];
       fi;
    fi;
od;

return fail;
end;

# input: list=[type(d,q), d, q, type(n,q)] acting as a subgroup 
# of some big type(n,q)
# output: list=[rr, dd] for a ppd(2*dd;q)-element rr
godown:=function(list)
local d, q, g, gg, i, r, pol, factors, degrees, newdim, power, rr, ss,
newgroup, colldegrees, exp, count, type, exps, setdegrees;

g:=list[1];
d:=list[2];
q:=list[3];
gg:=list[4];
#type:=list[5];

Print(d,"\c");
#find an element with irreducible action of relative prime dimension to 
#all other invariant subspaces
#count is just safety, if things go very bad
count:=0;

repeat 
   count:=count+1;
Print(".\c");
   r:=PseudoRandom(g);
   pol:=CharacteristicPolynomial(r);
   factors:=Factors(pol);
   degrees:=AsSortedList(List(factors,Degree));
   newdim:=firsthalf(degrees);
until (count>100) or (newdim <> fail and newdim<=Maximum(2,d/4));

if count>100 then
   return fail;
fi;

# raise r to a power so that acting trivially outside one invariant subspace
degrees:=Filtered(degrees, x->x<>newdim);
colldegrees:=Collected(degrees);
   setdegrees:=Set(degrees);
   exps:=[];
   for i in [1..Length(setdegrees)] do
      if newdim > 2 then 
         exps[i]:=q^setdegrees[i]-1;
      else
         if setdegrees[i] mod 2 = 0 then
            exps[i]:=q^(setdegrees[i]/2)+1;
         else
            exps[i]:=q^setdegrees[i]-1;
         fi;
      fi;
    od;
    power:=Lcm(exps)*q;
   
# power further to cancel q-part of element order
if degrees[1]=1 then 
   exp:=colldegrees[1][2]-(DimensionOfMatrixGroup(gg)-d);
   if exp>0 then 
     power:=power*q^exp;
   fi;
fi;
rr:=r^power;

#conjugate rr to hopefully get a smaller dimensional classical
#ss:=rr^PseudoRandom(gg);
#newgroup:=Group(rr,ss);

return [rr,newdim];
end;

# input is (group,dimension,q)
# output is a group element acting irreducibly in two dimensions, and fixing
# a (dimension-2)-dimensional subspace
constructppd2:=function(g,dim,q)
local out, list ;

list:=[g,dim,q,g];
repeat
   out:=godown(list);
   if out=fail or out[1]*out[1]=One(out[1]) then 
      Print("B\c");
      list:=[g,dim,q,g];
      out:=fail;
   else
      if out[2]>2 then 
         list:=[Group(out[1],out[1]^PseudoRandom(g)),2*out[2],q,g];
      fi;
   fi;
until out<>fail and out[2]=2;

return out[1];

end;

constructsl4:=function(g,dim,q,r)
local s,h,count,readydim4,readydim3,ready,u,orderu,
      nullr,nulls,nullspacer,nullspaces,int,intbasis,nullintbasis,
      newu,newbasis,newbasisinv,newr,news,outputu,mat,i,shorts,shortr;
nullr:=NullspaceMat(r-One(r));
nullspacer:=VectorSpace(GF(q),nullr);
mat:=One(r);
ready:=false;
repeat 
  s:=r^PseudoRandom(g);
  nulls:=NullspaceMat(s-One(s));
  nullspaces:=VectorSpace(GF(q),nulls);
  int:=Intersection(nullspacer,nullspaces);
  intbasis:=Basis(int);
  newbasis:=[];
  for i in [1..Length(intbasis)] do
      Add(newbasis,intbasis[i]);
  od;
  i:=0;
  repeat 
     i:=i+1;
     if not mat[i] in int then
        Add(newbasis,mat[i]);
        int:=VectorSpace(GF(q),newbasis);
     fi;
  until Dimension(int)=dim;
  ConvertToMatrixRep(newbasis);
  newbasisinv:=newbasis^(-1);
  newr:=newbasis*r*newbasisinv;
  news:=newbasis*s*newbasisinv;

  #shortr, shorts do not need memory
  #we shall throw away the computations in h
  #check that we have SL(4,q), by non-constructive recognition
  shortr:=newr{[dim-3..dim]}{[dim-3..dim]};
  shorts:=news{[dim-3..dim]}{[dim-3..dim]};  
  h:=Group(shortr,shorts);
  count:=0;
  readydim4:=false;
  readydim3:=false;
  repeat
     u:=PseudoRandom(h);
     orderu:=Order(u);
     if orderu mod ((q^4-1)/(q-1)) = 0 then
        readydim4:=true;
     elif Gcd(orderu,(q^2+q+1)/Gcd(3,q-1))>1 then 
        readydim3:=true;
     fi;
     if readydim4 = true and readydim3 = true then
        ready:=true;
        break;
     fi;
     count:=count+1;
  until count=30;
until ready=true;

return Group(r,s);
end;

linearaction := function(bas,q,el)
  local mat,vecs;
  vecs := BasisVectors(bas);
  mat := List(vecs,v->Coefficients(bas,v*el));
  ConvertToMatrixRep(mat,GF(q));
  return mat;
end;




#g=SL(d,q), given as a subgroup of SL(dim,q)
#output: [SL(2,q), and a basis for the 2-dimensional subspace where it acts
godownfromd:=function(g,q,d,dim)
local y,yy,ready,order,es,dims,subsp,z,x,a,b,c,h,vec,vec2,
pol,factors,degrees,comm1,comm2,comm3,image,basis,action,vs,readyqpl1,
readyqm1,count,u,orderu;

repeat 
  ready:=false;
  y:=PseudoRandom(g);
  pol:=CharacteristicPolynomial(y);
  factors:=Factors(pol);
  degrees:=List(factors,Degree);
  if d-1 in degrees then 
     order:=Order(y);
     if order mod (q-1)=0 then
        yy:=y^(order/(q-1));
     else 
        yy:=One(y);
     fi;
     if not IsOne(yy) then 
          es:= Eigenspaces(GF(q),yy);
          dims:=List(es,Dimension);
          if IsSubset(Set([1,d-1,dim-d]),Set(dims)) and
             1 in Set(dims) then
             es:=Filtered(es,x->Dimension(x)=1);
             vec:=Basis(es[1])[1];
             #next line can happen only with dim=d+1
             if vec*yy=vec then 
                vec:=Basis(es[2])[1];
             fi;
             repeat 
                z:=PseudoRandom(g);
                x:=yy^z;
                a:=Comm(x,yy);
                b:=a^yy;
                c:=a^x;
                comm1:= Comm(a,c);
                comm2:=Comm(a,b);
                comm3:=Comm(b,c);
                if comm1<>One(a) and comm2<>One(a) and 
                  comm3<>One(a) and Comm(comm1,comm2)<>One(a) then
                  vec2:=vec*z;
                  vs:=VectorSpace(GF(q),[vec,vec2]);
                  basis:=Basis(vs);
                  #check that the action in 2 dimensions is SL(2,q)
                  #by non-constructive recognition, finding elements of
                  #order (q-1) and (q+1)
                  #we do not need memory in the group image
                  action:=List([a,b,c],x->linearaction(basis,q,x));
                  image:=Group(action);
                  count:=0;
                  readyqpl1:=false;
                  readyqm1:=false;
                  repeat
                     u:=PseudoRandom(image);
                     orderu:=Order(u);
                     if orderu = q-1 then 
                        readyqm1:=true;
                     elif orderu = q+1 then 
                        readyqpl1:=true;
                     fi;
                     if readyqm1 = true and readyqpl1 = true then
                        ready:=true;
                        break;
                     fi;
                     count:=count+1;
                   until count=20;
                fi;
             until ready=true;
          fi;
     fi;
  fi;
until ready;

h:=Group(a,b,c);
subsp:=VectorSpace(GF(q),[vec,vec2]);
return [h,subsp];

end;

#input: g=SL(3,q)
#output: [SL(2,q), and a basis for the 2-dimensional subspace where it acts
godownfrom3:=function(g,q)
local y,yy,ready,order,es,dims,subsp,z,x,a,b,c,h,vec,vec2,
pol,factors,degrees,comm1,comm2,comm3,image,basis,action,vs,readyqpl1,
readyqm1,count,u,orderu;

repeat 
  ready:=false;
  y:=PseudoRandom(g);
  pol:=CharacteristicPolynomial(y);
  factors:=Factors(pol);
  degrees:=List(factors,Degree);
  if 2 in degrees then 
     order:=Order(y);
     if order mod (q-1)=0 then
        yy:=y^(order/(q-1));
     else 
        yy:=One(y);
     fi;
     if not IsOne(yy) then 
          es:= Eigenspaces(GF(q),yy);
          dims:=List(es,Dimension);
          if [1,2]=Set(dims) then 
             es:=Filtered(es,x->Dimension(x)=1);
             vec:=Basis(es[1])[1];
             repeat 
                z:=PseudoRandom(g);
                x:=yy^z;
                a:=Comm(x,yy);
                b:=a^yy;
                c:=a^x;
                comm1:= Comm(a,c);
                comm2:=Comm(a,b);
                comm3:=Comm(b,c);
                if comm1<>One(a) and comm2<>One(a) and 
                  comm3<>One(a) and Comm(comm1,comm2)<>One(a) then
                  vec2:=vec*z;
                  vs:=VectorSpace(GF(q),[vec,vec2]);
                  basis:=Basis(vs);
                  #check that the action in 2 dimensions is SL(2,q)
                  #by non-constructive recognition, finding elements of
                  #order (q-1) and (q+1)
                  #we do not need memory in the group image
                  action:=List([a,b,c],x->linearaction(basis,q,x));
                  image:=Group(action);
                  count:=0;
                  readyqpl1:=false;
                  readyqm1:=false;
                  repeat
                     u:=PseudoRandom(image);
                     orderu:=Order(u);
                     if orderu = q-1 then 
                        readyqm1:=true;
                     elif orderu = q+1 then 
                        readyqpl1:=true;
                     fi;
                     if readyqm1 = true and readyqpl1 = true then
                        ready:=true;
                        break;
                     fi;
                     count:=count+1;
                   until count=20;
                fi;
             until ready=true;
          fi;
     fi;
  fi;
until ready;

h:=Group(a,b,c);
subsp:=VectorSpace(GF(q),[vec,vec2]);
return [h,subsp];

end;

#####################################################
#going down from 4 to 2 dimensions, when q=2,3,4,5,9
#just construct the 4-dimensional invariant space and generators
#for the group acting on it
exceptionalgodown:=function(h,q,dim)
local basis, v, vs, i, gen;

vs:=VectorSpace(GF(q),One(h));
basis:=[];
repeat 
   Print("C");
   for i in [1..4] do 
      v:=PseudoRandom(vs);
      for gen in GeneratorsOfGroup(h) do
         Add(basis,v*gen-v);
      od;
   od;
   basis:=ShallowCopy(SemiEchelonMat(basis).vectors);
until Length(basis)=4;
return [h,VectorSpace(GF(q),basis)];
end;


constructsl2:=function(g,d,q,type)
local r,h;

r:=constructppd2(g,d,q,type);
h:=constructsl4(g,d,q,r);
if not (q in [2,3,4,5,9]) then 
   return godownfromd(h,q,4,d);
else
   return exceptionalgodown(h,q,d);
#   return ["sorry only SL(4,q)",h]
fi;
end;

#experiment with 2-dim irreducible and conjugate,whether they generate
#Sp(4,q)
testq:=function(q)
local d,g,out,out2,h,s;

d:=100;
g:=Sp(100,q);
out:=constructppd2(g,d,q);
out2:=out^PseudoRandom(g);
h:=Group(out,out2);
s:=StabilizerChain(h);
return Size(s)/Size(SP(4,q));
end;

#experiment with 2-dim irreducible and conjugate,whether they generate
#Sp(4,q)
testqout:=function(q,out)
local d,g,out2,out3,h,s;

d:=100;
g:=Sp(100,q);
out2:=out^PseudoRandom(g);
#out3:=out^PseudoRandom(g);
h:=Group(out,out2);
s:=StabilizerChain(h);
return Size(s)/Size(SP(4,q));
end;

experiment2 := function(g,x)
  local bas,d,f,i,l,ll,lll,llll,q,r,s,y;
  f := FieldOfMatrixGroup(g);
  q := Size(f);
  d := DimensionOfMatrixGroup(g);
  y := RECOG.FindOrder3Element(g);
  l := [x,x^y,x^(y^2)];
  ll := List(l,a->SemiEchelonMat(a-One(a)).vectors);
  lll := List(ll,m->VectorSpace(f,m));
  s := Sum(lll);
  if Dimension(s) = 6 then
      Print("6\c");
      return "dim6";
  fi;
  bas := Basis(s);
  llll := List(l,x->RECOG.LinearAction(bas,f,x));
  for i in [1..10] do
      r := RecogniseClassical(Group(llll));
      if r.IsSpContained <> "unknown" then break; fi;
  od;
  Print(r.IsSpContained);
  return r.IsSpContained;
end;

experiment1 := function(g)
  local d,f,q,x;
  f := FieldOfMatrixGroup(g);
  q := Size(f);
  d := DimensionOfMatrixGroup(g);
  x := constructppd2(g,d,q);
  return x;
end;
  
