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

RECOG.SL_Even_godownone:=function(g,subspg,q,d)
local n,y,yy,yyy,ready,order,es,null,subsph,z,x,a,b,c,h,r,divisors,cent,i,
pol,factors,degrees;

n:=DimensionOfMatrixGroup(g);
#d:=Dimension(subspg);
repeat 
  ready:=false;
  y:=PseudoRandom(g);
  pol:=CharacteristicPolynomial(GF(q),GF(q),StripMemory(y),1);
  factors:=Factors(pol);
  degrees:=List(factors,Degree);
  if d-1 in degrees then 
     order:=Order(y);
     yy:=y^(order/Gcd(order,q-1));
     if not IsOne(yy) then 
          es:= Eigenspaces(GF(q),StripMemory(yy));
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
gens,degrees,factors,pol,ready,ready2,ready3,z;

n:=DimensionOfMatrixGroup(g);

if q-1>n then 
  subspg:=VectorSpace(GF(q),One(g));
  subgplist:=[g,subspg];
  workingdim:=n;
  while workingdim > 2 do
    subgplist:=RECOG.SL_Even_godownone(subgplist[1],subgplist[2],q,workingdim);
    workingdim:=workingdim-1;
  od;
else
  #case of small q
  repeat  
    ready:=false;
    y:=PseudoRandom(g);
    pol:=CharacteristicPolynomial(GF(q),GF(q),StripMemory(y),1);
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
       pol:=CharacteristicPolynomial(GF(q),GF(q),StripMemory(z),1);
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
  
  subgplist:=RECOG.SL_Even_godownone(h,VectorSpace(GF(q),One(g)),q,3);
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
  # by left-multiplying with an expression in the standard generators:
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

RECOG.ExpressInStd_SL2 := function(m,r)
  if not(IsOne(m[1][1])) then
      if IsZero(m[2][1]) then
          RECOG.DoRowOp_SL(m,2,1,r.one,r);
          # Now m[2][1] is non-zero
      fi;
      RECOG.DoRowOp_SL(m,1,2,(r.one-m[1][1])/m[2][1],r);
  fi;
  # Now m[1][1] is equal to one
  if not(IsZero(m[2][1])) then
      RECOG.DoRowOp_SL(m,2,1,-m[2][1],r);
  fi;
  # Now m[2][1] is equal to zero and thus m[2][2] equal to zero
  if not(IsZero(m[1][2]) then
  RECOG.DoRowOp_SL(m,1,2,-m[1][2],r);
  # Now m is the identity matrix, the element collected in r
  # is the one to multiply on the left hand side to transform m to the
  # identity. Thus it is equal to the inverse of m.
end;

RECOG.FindStdGens_SL_EvenChar := function(sld,sl2,bas,p,ext)
  # gens of sld must be gens for SL(d,q) in its natural rep with memory
  # sl2 < SL(d,q) of isotype SL(2,q) in std gens acting on the subspace
  # of dimension 2 given by bas (mutable), we assume that sl2 gens are
  # expressed in terms of gens, furthermore, the group sl2 must have
  # an d-2 - dimensional fixed space.
  # This function extends bas to a basis of the full row space
  # and returns an slp such that


  f := GF(p,ext);
  q := Size(f);

  n := 2;
  sl2gens := GeneratorsOfGroup(sl2);
  V := VectorSpace(f,bas);
  b := Basis(V,bas);
  sl2genss := List(sl2gens,x->List(BasisVectors(b),v->Coefficients(b,v*x)));
  sl2genss := GeneratorsWithMemory(slp2genss);
  resl2 := RECOG.RecogniseSL2NaturalEvenChar(Group(sl2genss),f,false);
  slp := SLPOfElms(re.std);
  bas := re.bas * bas;
  masi := re.masi;
  mati := re.mati;

  fakegens := ListWithIdenticalEntries(Length(GeneratorsOfGroup(sld)),());
  fakegens := GeneratorsWithMemory(fakegens);
  sl2std := ResultOfStraightLineProgram(slp,fakegens);

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

  
RECOG.RecogniseSL2NaturalEvenChar := function(g,f,torig)
  # f a finite field, g equal to SL(2,Size(f)), t either an element
  # of order p = Characteristic(f) or false.
  # Returns a set of standard generators for SL_2 and the base change
  # to expose it. Works with memory. Uses PseudoRandom.
  local a,actpos,am,b,bas,bm,c,can,ch,cm,co,co2,deg,el,ev,eva,evb,evbi,
        gens,i,j,k,kk,mas,masi,mat,mati,mb,o,one,os,p,pos,q,ss,ssm,t,tb,
        tm,tt,ttm,u,v,x,xb,xm;
  q := Size(f);
  p := Characteristic(f);
  deg := DegreeOverPrimeField(f);
  gens := GeneratorsOfGroup(g);
  if torig = false then
      i := 1;
      while i <= Length(gens) do
          if not(IsOne(gens[i])) and IsOne(gens[i]^2) then
              torig := gens[i];
              break;
          fi;
          i := i + 1;
      od;
  fi;
  if torig = false then
      repeat
          am := PseudoRandom(g);
      until Order(am) = q-1;
      a := StripMemory(am);
      eva := Eigenvectors(f,a);
      repeat
          bm := am^PseudoRandom(g);
      until am*bm<>bm*am;
      b := StripMemory(bm);
      ev := Eigenvalues(f,b);
      evb := List(ev,v->NullspaceMat(b-v*One(b))[1]);
      evbi := evb^-1;
      c := evb*a*evbi;
      if IsZero(c[1][2]) or IsZero(c[2][1]) then
          # We were lucky, a and b share an eigenspace
          tm := Comm(am,bm);
      else
          u := eva[1]*evbi;
          # We know that both components are non-zero since a and b do not
          # have a common eigenspace!
          repeat
              cm := am^PseudoRandom(g);
              c := StripMemory(cm);
              v := (eva[1]*c)*evbi;
          until not(IsZero(v[1]) or IsZero(v[2]));
          pos := LogFFE((v[2]/v[1])/(u[2]/u[1]),ev[2]);
          if IsOddInt(pos) then
              pos := (pos + q - 1) / 2;
          else
              pos := pos / 2;
          fi;
          tm := Comm(am,bm^pos*cm^-1);
          if Order(tm) <> 2 then Error(2); fi;
      fi;
  else
      tm := torig;
  fi;
  t := StripMemory(tm);
  ch := Factors(CharacteristicPolynomial(f,f,t,1));
  if Length(ch) <> 2 or ch[1] <> ch[2] then
      Error("how could this have happened?");
  fi;
  one := OneMutable(t);
  bas := MutableCopyMat(NullspaceMat(Value(ch[1],t)));
  Add(bas,one[1]);
  if RankMat(bas) < 2 then
      bas[2] := one[2];
  fi;
  tb := bas*t*bas^-1;
  can := CanonicalBasis(f);
  tt := [t];
  ttm := [tm];
  mat := [Coefficients(can,tb[2][1])];
  mb := MutableBasis(GF(2),mat);
  o := [gens[1]];
  os := [gens[1]];
  actpos := 1;
  j := 1;
  while Length(tt) < deg do
      repeat
          repeat
              while j > Length(o) do
                  for k in gens do
                      kk := o[actpos]*k;
                      pos := PositionSorted(os,kk);
                      if pos > Length(os) or os[pos] <> kk then
                          Add(o,kk);
                          Add(os,kk,pos);
                      fi;
                  od;
                  actpos := actpos + 1;
              od;
              xm := o[j];
              j := j + 1;
              c := Comm(tm,xm);
          until not(IsOne(c^2));
          xm := xm * c^(((q-1)*(q+1)-1)/2);
          x := StripMemory(xm);
          xb := bas*x*bas^-1;
          co := Coefficients(can,xb[2][1]);
      until not(IsContainedInSpan(mb,co));
      CloseMutableBasis(mb,co);
      Add(tt,x);
      Add(ttm,xm);
      Add(mat,co);
      #Print(".\c");
  od;
  #Print(j-1,"\n");
  ConvertToMatrixRep(mat,2);
  mati := mat^-1;

  # Now we can add an arbitrary multiple of the first row to the
  # second and an arbitrary multiple of the second column to the first.
  # Therefore we quickly find other complimentary transvections:
  ss := [];
  ssm := [];
  mas := [];
  mb := MutableBasis(GF(2),mas,ZeroMutable(mat[1]));
  j := 1;
  while Length(ss) < deg do
      while true do   # will be left by break
          repeat
              while j > Length(o) do
                  for k in gens do
                      kk := o[actpos]*k;
                      pos := PositionSorted(os,kk);
                      if pos > Length(os) or os[pos] <> kk then
                          Add(o,kk);
                          Add(os,kk,pos);
                      fi;
                  od;
                  actpos := actpos + 1;
              od;
              xm := o[j];
              j := j + 1;
              x := MutableCopyMat(bas*StripMemory(xm)*bas^-1);
          until not(IsZero(x[1][2]));
          if not(IsOne(x[2][2])) then
              el := (One(f)-x[2][2])/x[1][2];
              co := Coefficients(can,el) * mati;
              for i in [1..Length(co)] do 
                  if not(IsZero(co[i])) then
                      xm := ttm[i] * xm;
                  fi;
              od;
              x[2] := x[2] + x[1] * el;
              if x <> bas*StripMemory(xm)*bas^-1 then Error("!!!"); fi;
          fi;
          # now x[2][2] is equal to One(f)
          # we postpone the actual computation of the final x until we
          # know it is needed:
          co := Coefficients(can,x[1][2]);
          if IsContainedInSpan(mb,co) then continue; fi;
          # OK, we need it, so let's make it:
          el := x[2][1];
          co2 := Coefficients(can,el) * mati;
          for i in [1..Length(co2)] do 
              if not(IsZero(co2[i])) then
                  xm := xm * ttm[i];
              fi;
          od;
          x := StripMemory(xm);
          # now x[2][1] is equal to Zero(f) and thus x[1][1] is One(f) as well
          break;
      od;
      CloseMutableBasis(mb,co);
      Add(ss,x);
      Add(ssm,xm);
      Add(mas,co);
      #Print(".\c");
  od;
  #Print("\n");
  ConvertToMatrixRep(mas,2);
  masi := mas^-1;

  return rec( g := g, std := Concatenation(ssm,ttm), t := tm, 
              mati := mati, masi := masi, bas := bas, basi := bas^-1 );
end;

RECOG.GuessSL2ElmOrder := function(x,q)
  local facts,i,j,o,p,r,s,y,z;
  if IsOne(x^(q-1)) then
      facts := Collected(FactInt(q-1:cheap)[1]);
      s := Product(facts,x->x[1]^x[2]);
      r := (q-1)/s;
  else
      facts := Collected(FactInt(q+1:cheap)[1]);
      s := Product(facts,x->x[1]^x[2]);
      r := (q+1)/s;
  fi;
  y := x^r;
  o := r;
  for i in [1..Length(facts)] do
      p := facts[i];
      j := p[2]-1;
      while j >= 0 do
          z := y^(s/p[1]^(p[2]-j));
          if not(IsOne(z)) then break; fi;
          j := j - 1;
      od;
      o := o * p[1]^(j+1);
  od;
  return o;
end;

