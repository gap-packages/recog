#############################################################################
##
##  classicalnatural.gi      
##                                recog package
##                                                        Max Neunhoeffer
##                                                            Ákos Seress
##
##  Copyright 2006-2009 by the authors.
##  This file is free software, see license information at the end.
##
##  Constructive recognition of classical groups in their natural
##  representation.
##
#############################################################################


RECOG.SL_Even_godownone:=function(g,subspg,q)
local n,d,y,yy,yyy,ready,order,es,null,subsph,z,x,a,b,c,h,r,divisors,cent,i,
pol,factors,degrees;

n:=DimensionOfMatrixGroup(g);
d:=Dimension(subspg);
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

RECOG.SL_Even_constructdata:=function(g,q)
local n,subgplist,subspg,i,j,r,hgens,output,h,workingdim,y,yy,order,
gens,degrees, factors, pol, ready,ready2,list,hmod,cf, fac,vs,z;

n:=DimensionOfMatrixGroup(g);

if q-1>n then 
  subspg:=VectorSpace(GF(q),One(g));
  subgplist:=[g,subspg];
  workingdim:=n;
  while workingdim > 2 do
    subgplist:=RECOG.SL_Even_godownone(subgplist[1],subgplist[2],q);
    workingdim:=workingdim-1;
  od;
else
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
  repeat
     gens:=[yy];
     Add(gens,yy^PseudoRandom(g));
     Add(gens,yy^PseudoRandom(g));
     h:=Group(gens);
     list:=[];
     for i in [1..10] do
       z:=PseudoRandom(h);
       pol:=CharacteristicPolynomial(z);
       factors:=Factors(pol);
       degrees:=List(factors,Degree);
       Add(list,Maximum(degrees));
     od;
     list:=Set(list);
     if 3 in list and 2 in list then 
       ready2:=true;
       hmod:=GModuleByMats(gens,GF(q));
       cf:=MTX.CompositionFactors(hmod);
       fac:=Filtered(cf,x->x.dimension=3);
       vs:=VectorSpace(GF(q), MTX.Homomorphisms(fac[1],hmod)[1]);
       subgplist:=RECOG.SL_Even_godownone(h,vs,q);
     fi;
   until ready2;
fi;

return subgplist;
end;

RECOG.FindStdGensUsingBSGS := function(g,stdgens,projective,large)
  # stdgens generators for the matrix group g
  # returns an SLP expressing stdgens in the generators of g
  # set projective to true for projective mode
  # set large to true if we should not bother finding nice base points!
  local S,dim,gens,gm,i,l,strong;
  dim := DimensionOfMatrixGroup(g);
  gm := GroupWithMemory(g);
  if HasSize(g) then SetSize(gm,Size(g)); fi;
  if large then
      S := StabilizerChain(gm,rec( Projective := projective,
        Cand := rec( points := One(g), 
                     ops := ListWithIdenticalEntries(dim, OnLines) ) ) );
  else
      S := StabilizerChain(gm,rec( Projective := projective ) );
  fi;
  strong := ShallowCopy(StrongGenerators(S));
  ForgetMemory(S);
  l := List(stdgens,x->SiftGroupElementSLP(S,x));
  gens := EmptyPlist(Length(stdgens));
  for i in [1..Length(stdgens)] do
      if not l[i].isone then return fail; fi;
      Add(gens,ResultOfStraightLineProgram(l[i].slp,strong));
  od;
  return SLPOfElms(gens);
end;

RECOG.InitSLSLP := function(p, ext, stdgens)
  local r,f;
  r := rec( t := stdgens[1], s := stdgens[2], a := stdgens[3],
            b := stdgens[4], c := stdgens[5], std := stdgens, 
            elm := stdgens[1]^0, q := p^ext, ext := ext, p := p,
            f := GF(p,ext), cb := CanonicalBasis(f),
            cache := [EmptyPlist(100),EmptyPlist(100),EmptyPlist(100)] );
  return r;
end;

RECOG.FindFFCoeffs := function(r,lambda)
  return IntVecFFE(Coefficients(r.cb,lambda));
end;

RECOG.SL_Even_DoRowOp := function(i,j,lambda,r)
  # add lambda times j-th row to i-th row, i<>j, lambda<>0
  # by left-multiplying with an expressing in the standard generators:
  #   t : e_n -> e_{n-1} -> ... -> e_1 -> *    where * in V_n
  #   s : e_n -> e_{n-1} -> ... -> e_2 -> e_n and e_1 -> e_1
  #   a : e_1 -> e_1+e_2, e_i -> e_i   for i > 1
  #   b : e_2 -> e_1+e_2, e_i -> e_i   for i <> 2
  #   c : e_1 -> omega e_1, e_2 -> omega^-1 e_2, e_i -> e_i for i > 2
  # Note that V_i = <e_1,...,e_i>.
  # So <a,b,c> is an SL_2 in the upper left corner, t is an n-cycle
  # with garbage in the first row, s is an n-1 cycle with garbage in the
  # first two rows.
  # Let q=2^k and call a_0 := a, a_1 := a^(c^(q/2)), a_i := a_1 ^ i
  #           and call b_0 := b, b_1 := b^(c^(-q/2)), b_i := b_1 ^ i
  # This only modifies the record r collecting a straight line program.
  local Getak,Getsj,Getti,coeffs,k,new;
  
  Getti := function(r,l)
      if not IsBound(r.cache[1][l]) then
          r.cache[1][l] := r.t^(l);
      fi;
      return r.cache[1][l];
  end;
  Getsj := function(r,l)
      if not IsBound(r.cache[2][l]) then
          r.cache[2][l] := r.s^l;
      fi;
      return r.cache[2][l];
  end;
  Getak := function(r,k)
      if not IsBound(r.cache[3][k]) then
          if k = 1 then
              r.cache[3][k] := r.a;
          else
              if not IsBound(r.cache[3][2]) then
                  r.cache[3][2] := r.a^(r.c^(r.q/2));
              fi;
              if k > 2 then
                  r.cache[3][k] := r.cache[3][2]^(k-1);
              fi;
          fi;
      fi;
      return r.cache[3][k];
  end;

  new := r.t^0;
  coeffs := RECOG.FindFFCoeffs(lambda,r.p,r.ext,r.q);
  for k in [1..r.ext] do
    if not(IsZero(coeffs[k])) then
      if i < j then
          # We need to multiply with the element
          #    t^(i-1) * s^(j-i-1) * a_k * s^-(j-i-1) * t^-(i-1)
          # from the left.
          if i > 1 then new := Getti(r,i-1)^-1 * new; fi;
          if j > i+1 then new := Getsj(r,j-i-1)^-1 * new; fi;
          new := Getak(r,k) * new;
          if j > i+1 then new := Getsj(r,j-i-1) * new; fi;
          if i > 1 then new := Getti(r,i-1) * new; fi;
      elif i > j then
          # We need to multiply with the element
          #    t^(j-1) * s^(i-j-1) * a_k * s^-(i-j-1) * t^-(j-1)
          # from the left.
          if i > 1 then new := Getti(r,j-1)^-1 * new; fi;
          if j > i+1 then new := Getsj(r,i-j-1)^-1 * new; fi;
          new := Getak(r,k) * new;
          if j > i+1 then new := Getsj(r,i-j-1) * new; fi;
          if i > 1 then new := Getti(r,j-1) * new; fi;
      fi;
    fi;
  od;
  r.elm := r.new * r.elm;
  return r.new;
end;

RECOG.MakeSL_Even_StdGens := function(p,ext,n,d)
  local a,b,c,f,q,s,t;
  f := GF(p,ext);
  q := Size(f);
  t := IdentityMat(d,f);
  t := t{Concatenation([n],[1..n-1],[n+1..d])};
  ConvertToMatrixRep(t,q);
  s := IdentityMat(d,f);
  s := s{Concatenation([1,n],[2..n-1],[n+1..d])};
  ConvertToMatrixRep(s,q);
  a := IdentityMat(d,f);
  a[1][2] := One(f);
  b := IdentityMat(d,f);
  b[2][1] := One(f);
  c := IdentityMat(d,f);
  c[1][1] := Z(q);
  c[2][2] := Z(q)^-1;
  return [t,s,a,b,c];
end;

RECOG.FindStdGens_SL_EvenChar := function(sld,sl2,bas,p,ext)
  # gens must be gens for SL(d,q) in its natural rep with memory
  # sl2 < SL(d,q) of isotype SL(2,q) in std gens acting on the subspace
  # of dimension 2 given by bas (mutable), we assume that sl2 gens are
  # expressed in terms of gens
local a,ax,b,c,d,f,fakegens,i,inter,n,news,newt,pos,q,r,sl2gens,u,t,x,y,z;

  f := GF(p,ext);
  q := Size(f);

  n := 2;
  sl2gens := GeneratorsOfGroup(sl2);

  a := sl2gens[1];
  b := sl2gens[2];
  c := sl2gens[3];
  
  fakegens := ListWithIdenticalEntries( 5+Length(GeneratorsOfGroup(sld)),());
  n := 2;
  while n < d do
      repeat
          x := PseudoRandom(sld);
          ax := a^x;
          u := bas * (ax-One(ax));
          inter := NullspaceMat(u);
      until Length(inter) = n-1;
      z := NullspaceMat(TransposedMat(inter))[1];
      # Now we would like to have an element y of sl_n with last column
      # being equal to TransposedMat(z).
      r := RECOG.InitSLSLP(p,ext,fakegens{[1..5]});
      if IsZero(z[n]) then
          pos := PositionNonZero(z);
          z := z * (z[pos]^-1);
          RECOG.SL_Even_DoRowOp(pos,n,One(f),r);
      else
          pos := n;
          z := z * (z[n]^-1);
      fi;
      for i in [1..n] do
          if i <> pos and not(IsZero(pos[i])) then
              RECOG.SL_Even_DoRowOp(i,pos,z[i],r);
          fi;
      od;
      y := r.elm;
      newt := t * ax^y;
      Add(bas,bas[n] * newt^-1);
      n := n + 1;
      news :=  1;
  od;

end;

  
