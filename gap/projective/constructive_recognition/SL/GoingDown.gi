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
#############################################################################



#############################################################################
#############################################################################
######## GoingDown method for special linear groups #########################
#############################################################################
#############################################################################



# TODO: Work on comments and documentation



# Find random element s = r^PseudRandom(g) such that <r,s> is isomorphic to SL(4,q)
# and check whether they are isomorphic
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
    
    # Remark D.R.: Tries to reduce matrix multiplications
    #               by working with 4 dimensional matrices
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
  Info(InfoRecog,2,"New Dimension: 2");
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
     if InfoLevel(InfoRecog) >= 3 then Print("C"); fi;
     for i in [1..4] do
        v:=PseudoRandom(vs);
        for gen in GeneratorsOfGroup(h) do
           Add(basis,v*gen-v);
        od;
     od;
     basis:=ShallowCopy(SemiEchelonMat(basis).vectors);
  until Length(basis)=4;
  Info(InfoRecog,2,"New Dimension: 2");
  return [h,VectorSpace(GF(q),basis)];
end;


RECOG.SLn_constructsl2:=function(g,d,q)
  local r,h;

  r := RECOG.constructppdTwoStingray(g,d,q,"SL",fail);
  Info(InfoRecog,2,"Finished main GoingDown, i.e. we found a stringray element which operates irreducible on a 2 dimensional subspace. \n");
  Info(InfoRecog,2,"Next goal: Find an random element s.t. the two elements generate SL(4,q). \n");
  h := RECOG.SLn_constructsl4(g,d,q,r);
  # Remark D.R.: at this point we know that h is isomorphic to SL(4,q)
  Info(InfoRecog,2,"Succesful. ");
  Info(InfoRecog,2,"Current Dimension: 4\n");
  Info(InfoRecog,2,"Next goal: Generate SL(2,q). \n");
  if not (q in [2,3,4,5,9]) then
     return RECOG.SLn_godownfromd(h,q,4,d);
  else
     return RECOG.SLn_exceptionalgodown(h,q,d);
  fi;
end;
