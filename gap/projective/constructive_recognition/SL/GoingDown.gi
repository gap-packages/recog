#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This files's authors include Max Neunhöffer, Ákos Seress, Daniel Rademacher.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
##
##  GoingDown method for special linear groups
##
#############################################################################

# finds a stingray element with a body of small dimension
# input: list=[SL(d,q), d, q, ...] acting as a subgroup of some big SL(n,q)
# output: list=[rr, dd, B] for a stingray element rr whose body B has
#   dimension dd
RECOG.godownStingraySL := function(list)
  local d, q, p, g, i, r, pol, factors, degrees, newdim, power, rr, max,
        colldegrees, count, check, ocount, beta, NiList, Maxi, qFactors,
        irrfact, invbase, firstSL;

  firstSL := function(list)
  local i, j, goodElement;
      for i in [1..Length(list)] do
          if list[i]>1 then
              if Gcd(list[i],Product(list)/list[i]) < list[i] then
                  return i;
              else
                  goodElement := true;
                  for j in [1..Length(list)] do
                      if not(j = i) and Gcd(list[i],list[j]) = list[i] then
                          goodElement := false;
                          break;
                      fi;
                  od;
                  if goodElement then
                      return i;
                  fi;
              fi;
          fi;
      od;
      return fail;
  end;

  g:=list[1];
  d:=list[2];
  q:=list[3];
  qFactors:=Factors(q);
  p := qFactors[1];

  max := Maximum([Log2Int(d),3]);

  # Overall count. Replace by formula and unequality
  ocount := 0;
  while ocount < 100 do

      #find an element with irreducible action of relative prime dimension to
      #all other invariant subspaces
      #count is just safety, if things go very bad
      count:=0;

      repeat
          count:=count+1;
          if InfoLevel(InfoRecog_ClassicalNatural) >= 3 then Print(".\c"); fi;
          r:=PseudoRandom(g);
          pol:=CharacteristicPolynomial(r);
          factors:=Factors(pol);
          degrees:=List(factors,Degree);
          newdim := firstSL(degrees);
      until (count>100) or (newdim <> fail and (degrees[newdim] < max));
      # Be careful if Log2Int(d) = 2! In this case we search for stingray elements with k < 2. Hence use newdim < Maximum([Log2Int(d),3])

      if count>100 then
          return fail;
      fi;

      # Split result from first:
      irrfact := factors[newdim];
      newdim := degrees[newdim];

      if newdim = 2 then
          check := true;
      else
          # Check whether the stingray candidate is a ppd-stingray element
          check := RECOG.IsPpdStingrayElement(p,Length(qFactors),newdim,irrfact);
      fi;

      if check then

          # raise r to a power so that acting trivially outside one invariant irreducible subspace
          NiList := Collected(degrees);
          NiList := Filtered(NiList,x->not(x[1] = newdim));
          colldegrees := List(NiList,x->x[1]);
          NiList := List(NiList,x->x[2]);
          Maxi := Maximum(NiList);
          beta := LogInt(Maxi,p);
          if not(p^beta = Maxi) then
              beta := beta + 1;
          fi;

          # power further to cancel q-part of element order
          power := Lcm(List(colldegrees, x->q^x-1))*p^beta;
          rr:=r^power;

          invbase := NullspaceMat(TransposedMat(RECOG.FixspaceMat(StripMemory(rr))));

          if newdim = 2 then
              if Size(invbase) = 2 then
                  return [rr,newdim,invbase];
              fi;
          else
              return [rr,newdim,invbase];
          fi;
      fi;

      ocount := ocount + 1;
  od;

  return fail;

end;

# input is (group,dimension,q)
# output is a group element acting irreducibly in two dimensions, and fixing
# a (dimension-2)-dimensional subspace
RECOG.constructppdTwoStingraySL := function(g,dim,q)
  local out, list, out2;

  Info(InfoRecog_ClassicalNatural,2,"  SL_n GoingDown: degree ",dim);

  list:=[g,dim,q];
  # exits only via the two returns: a stingray element of dimension 2
  repeat
     out:=RECOG.godownStingraySL(list);
     if out=fail or IsOne(out[1]^2) then
        Info(InfoRecog_ClassicalNatural,3,"    SL_n GoingDown: no stingray element, restart");
        list:=[g,dim,q];
        out:=fail;
     else
        if out[2] = 2 then
          return out[1];
        fi;
        Assert(1, out[2] >= 2);
        repeat
             out2:=RECOG.godownStingraySL(list);
             if out2=fail or IsOne(out2[1]^2) then
                 Info(InfoRecog_ClassicalNatural,3,"    SL_n GoingDown: no second stingray element, retry");
                 list:=[g,dim,q];
                 out2:=fail;
             fi;
        until out2<>fail and out2[2] >= 2;
        if out2[2] = 2 then
            return out2[1];
        fi;
        if RECOG.CheckNewStingrayGroup(out[1],out[3],out2[1],out2[3],q) then
             list:=[Group(out[1],out2[1]),out[2]+out2[2],q];
             Info(InfoRecog_ClassicalNatural,2,"  SL_n GoingDown: bodies of dimension ",
                  out[2]," and ",out2[2],", degree ",out[2]+out2[2]);
        else
             Info(InfoRecog_ClassicalNatural,3,"    SL_n GoingDown: stingray elements do not fit, restart");
             list:=[g,dim,q];
             out:=fail;
        fi;
     fi;
  until false;

end;

RECOG.SLn_constructsl4:=function(g,dim,q,r)
  local s,h,count,readydim4,readydim3,ready,u,orderu,
        nullr,nulls,nullspacer,nullspaces,int,intbasis,nullintbasis,
        newu,newbasis,newbasisinv,newr,news,outputu,mat,i,shorts,shortr;
  nullr:=RECOG.FixspaceMat(StripMemory(r));
  nullspacer:=VectorSpace(GF(q),nullr);
  mat:=One(r);
  ready:=false;
  repeat
    s:=r^PseudoRandom(g);
    nulls:=RECOG.FixspaceMat(StripMemory(s));
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


#g=SL(d,q), given as a subgroup of SL(dim,q)
#output: [SL(2,q), and a basis for the 2-dimensional subspace where it acts
RECOG.SLn_godownfromd:=function(g,q,d,dim)
  local y,yy,ready,order,es,dims,subsp,z,x,a,b,c,h,vec,vec2,
  pol,factors,degrees,comm1,comm2,comm3,image,basis,action,vs,readyqpl1,
  readyqm1,count,u,orderu,expecteddims;

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
            # Since yy^(q-1)=1, yy is semisimple over GF(q).  We want
            # one 1-space, one (d-1)-space, and the fixed outside space
            # of dimension dim-d; the last one is absent when dim=d.
            expecteddims:=Filtered([1,d-1,dim-d], x -> x > 0);
            if AsSortedList(dims)=AsSortedList(expecteddims) then
               es:=Filtered(es,x->Dimension(x)=1);
               vec:=Basis(es[1])[1];
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
                    action:=List([a,b,c],x->RECOG.LinearAction(basis,q,x));
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

#going down from 4 to 2 dimensions, when q=2,3,4,5,9
#just construct the 4-dimensional invariant space and generators
#for the group acting on it
RECOG.SLn_exceptionalgodown:=function(h,q,dim)
  local basis, v, vs, i, gen;

  vs:=VectorSpace(GF(q),One(h));
  basis:=[];
  repeat
     Info(InfoRecog_ClassicalNatural,3,"    SL_n GoingDown: looking for the SL(4,",q,") space");
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


RECOG.SLn_constructsl2:=function(g,d,q)
  local r,h;

  r:=RECOG.constructppdTwoStingraySL(g,d,q);
  h:=RECOG.SLn_constructsl4(g,d,q,r);
  if not (q in [2,3,4,5,9]) then
     return RECOG.SLn_godownfromd(h,q,4,d);
  else
     return RECOG.SLn_exceptionalgodown(h,q,d);
  #   return ["sorry only SL(4,q)",h];
  fi;
end;
