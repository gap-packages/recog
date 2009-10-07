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
local degrees,factors,gens,h,i,n,o,order,pol,ready,ready2,ready3,
      subgplist,subspg,w,workingdim,ww,www,y,yy,z;

n:=DimensionOfMatrixGroup(g);

if q-1>n then 
  subspg:=VectorSpace(GF(q),One(g));
  subgplist:=[g,subspg];
  workingdim:=n;
  while workingdim > 2 do
    subgplist:=RECOG.SL_Even_godownone(subgplist[1],subgplist[2],q,workingdim);
    workingdim:=workingdim-1;
    Print(workingdim," \c");
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
       yy := y^(q^(n-2)-1);
       if not(IsOne(yy)) and IsOne(yy^2) then ready := true; fi;
    fi;
  until ready;
  if q=2 then
    repeat
      z := yy^PseudoRandom(g);
    until Order(z*yy) = 3;
    o := OneMutable(z);
    i := 1;
    while i <= n do
      w := o[i]*yy-o[i];
      if not(IsZero(w)) then break; fi;
      i := i + 1;
    od;
    i := 1;
    while i <= n do
      ww := o[i]*z-o[i];
      if not(IsZero(ww)) then break; fi;
      i := i + 1;
    od;
    return [Group(z,yy),VectorSpace(GF(2),[w,ww])];
  fi;

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
  
  if q = 4 then
    o := One(h);
    i := 1;
    while i <= n do
      w := o[i]*GeneratorsOfGroup(h)[1]-o[i];
      if not(IsZero(w)) then break; fi;
      i := i + 1;
    od;
    i := 1;
    while i <= n do
      ww := o[i]*GeneratorsOfGroup(h)[2]-o[i];
      if not(IsZero(ww)) then break; fi;
      i := i + 1;
    od;
    while i <= n do
      www := o[i]*GeneratorsOfGroup(h)[3]-o[i];
      if not(IsZero(www)) then break; fi;
      i := i + 1;
    od;
    return [h,VectorSpace(GF(q),[w,ww,www])];
  fi;
      
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

RECOG.ResetSLstd := function(r)
  r.left := One(r.a);
  r.right := One(r.a);
  r.cache := [EmptyPlist(100),EmptyPlist(100)];
  return r;
end;
  
RECOG.InitSLstd := function(f,d,s,t,a,b)
  local r;
  r := rec( f := f, p := Characteristic(f), ext := DegreeOverPrimeField(f),
            q := Size(f), d := d, all := Concatenation(s,t,[a],[b]),
            one := One(f), One := One(s[1]), s := s, t := t, a := a, b := b );
  return RECOG.ResetSLstd(r);
end;

RECOG.FindFFCoeffs := function(r,lambda)
  return IntVecFFE(Coefficients(CanonicalBasis(r.f),lambda));
end;

RECOG.InitSLfake := function(f,d)
  local ext,l;
  ext := DegreeOverPrimeField(f);
  l := ListWithIdenticalEntries(2*ext+2,());
  l := GeneratorsWithMemory(l);
  return RECOG.InitSLstd(f,d,l{[1..ext]},l{[ext+1..2*ext]},
                         l[2*ext+1],l[2*ext+2]);
end;

RECOG.DoRowOp_SL := function(m,i,j,lambda,std)
  # add lambda times j-th row to i-th row, i<>j
  # by left-multiplying with an expression in the standard generators:
  #   a : e_n -> e_{n-1} -> ... -> e_1 -> e_n
  #   b : e_n -> e_{n-1} -> ... -> e_2 -> e_n and e_1 -> e_1
  #   s : e_1 -> e_1+ * e_2, e_i -> e_i   for i > 1
  #   t : e_2 -> e_1+ * e_2, e_i -> e_i   for i <> 2
  # s and t are lists of length ext to span over GF(p) all the scalars
  # in *.
  # Note that V_i = <e_1,...,e_i>.
  # So <s,t> is an SL_2 in the upper left corner, a is an n-cycle
  # b is an n-1 cycle with garbage fixing the first vector
  # This only modifies the record std collecting a straight line program.
  local Getai,Getbj,coeffs,k,new;
  
  Getai := function(l)
      if not IsBound(std.cache[1][l]) then
          std.cache[1][l] := std.a^(l);
      fi;
      return std.cache[1][l];
  end;
  Getbj := function(l)
      if not IsBound(std.cache[2][l]) then
          std.cache[2][l] := std.b^l;
      fi;
      return std.cache[2][l];
  end;

  new := std.One;
  coeffs := RECOG.FindFFCoeffs(std,lambda);
  for k in [1..std.ext] do
    if not(IsZero(coeffs[k])) then
      if i < j then
          # We need to multiply from the left with the element
          #    a^(i-1) * b^(j-i-1) * s_k * b^-(j-i-1) * a^-(i-1)
          # from the left.
          if i > 1 then new := Getai(i-1)^-1 * new; fi;
          if j > i+1 then new := Getbj(j-i-1)^-1 * new; fi;
          new := std.s[k] * new;
          if j > i+1 then new := Getbj(j-i-1) * new; fi;
          if i > 1 then new := Getai(i-1) * new; fi;
      elif i > j then
          # We need to multiply from the left with the element
          #    a^(j-1) * b^(i-j-1) * t_k * b^-(i-j-1) * a^-(j-1)
          # from the left.
          if j > 1 then new := Getai(j-1)^-1 * new; fi;
          if i > j+1 then new := Getbj(i-j-1)^-1 * new; fi;
          new := std.t[k] * new;
          if i > j+1 then new := Getbj(i-j-1) * new; fi;
          if j > 1 then new := Getai(j-1) * new; fi;
      fi;
    fi;
  od;
  std.left := new * std.left;
  if m <> false and not(IsZero(lambda)) then m[i] := m[i] + m[j] * lambda; fi;
  return new;
end;

RECOG.DoColOp_SL := function(m,i,j,lambda,std)
  # add lambda times i-th column to j-th column, i<>j
  # by left-multiplying with an expression in the standard generators:
  #   a : e_n -> e_{n-1} -> ... -> e_1 -> e_n
  #   b : e_n -> e_{n-1} -> ... -> e_2 -> e_n and e_1 -> e_1
  #   s : e_1 -> e_1+ * e_2, e_i -> e_i   for i > 1
  #   t : e_2 -> e_1+ * e_2, e_i -> e_i   for i <> 2
  # s and t are lists of length ext to span over GF(p) all the scalars
  # in *.
  # Note that V_i = <e_1,...,e_i>.
  # So <s,t> is an SL_2 in the upper left corner, a is an n-cycle
  # b is an n-1 cycle with garbage fixing the first vector
  # This only modifies the record std collecting a straight line program.
  local Getai,Getbj,coeffs,k,new;
  
  Getai := function(l)
      if not IsBound(std.cache[1][l]) then
          std.cache[1][l] := std.a^(l);
      fi;
      return std.cache[1][l];
  end;
  Getbj := function(l)
      if not IsBound(std.cache[2][l]) then
          std.cache[2][l] := std.b^l;
      fi;
      return std.cache[2][l];
  end;

  new := std.One;
  coeffs := RECOG.FindFFCoeffs(std,lambda);
  for k in [1..std.ext] do
    if not(IsZero(coeffs[k])) then
      if i < j then
          # We need to multiply from the right with the element
          #    a^(i-1) * b^(j-i-1) * s_k * b^-(j-i-1) * a^-(i-1)
          # from the left.
          if i > 1 then new := Getai(i-1)^-1 * new; fi;
          if j > i+1 then new := Getbj(j-i-1)^-1 * new; fi;
          new := std.s[k] * new;
          if j > i+1 then new := Getbj(j-i-1) * new; fi;
          if i > 1 then new := Getai(i-1) * new; fi;
      elif i > j then
          # We need to multiply from the right with the element
          #    a^(j-1) * b^(i-j-1) * t_k * b^-(i-j-1) * a^-(j-1)
          # from the left.
          if j > 1 then new := Getai(j-1)^-1 * new; fi;
          if i > j+1 then new := Getbj(i-j-1)^-1 * new; fi;
          new := std.t[k] * new;
          if i > j+1 then new := Getbj(i-j-1) * new; fi;
          if j > 1 then new := Getai(j-1) * new; fi;
      fi;
    fi;
  od;
  std.right := std.right * new;
  if m <> false and not(IsZero(lambda)) then 
      for k in [1..Length(m)] do
          m[k][j] := m[k][j] + m[k][i] * lambda; 
      od;
  fi;

  return new;
end;

RECOG.MakeSL_StdGens := function(p,ext,n,d)
  local a,b,f,i,q,s,t,x,res;
  f := GF(p,ext);
  q := Size(f);
  a := IdentityMat(d,f);
  a := a{Concatenation([n],[1..n-1],[n+1..d])};
  ConvertToMatrixRep(a,q);
  b := IdentityMat(d,f);
  b := b{Concatenation([1,n],[2..n-1],[n+1..d])};
  ConvertToMatrixRep(b,q);
  s := [];
  t := [];
  for i in [0..ext-1] do
      x := IdentityMat(d,f);
      x[1][2] := Z(p,ext)^i;
      Add(s,x);
      x := IdentityMat(d,f);
      x[2][1] := Z(p,ext)^i;
      Add(t,x);
  od;
  res := rec( s := s, t := t, a := a, b := b, f := f, q := q, p := p,
              ext := ext, One := IdentityMat(d,f), one := One(f),
              d := d );
  res.all := Concatenation( res.s, res.t, [res.a], [res.b] );
  return res;
end;

RECOG.ExpressInStd_SL2 := function(m,std)
  local mi;

  if IsObjWithMemory(m) then
      mi := InverseMutable(StripMemory(m));
  else
      mi := InverseMutable(m);
  fi;
  std.left := std.One;
  if not(IsOne(mi[1][1])) then
      if IsZero(mi[2][1]) then
          RECOG.DoRowOp_SL(mi,2,1,std.one,std);
          # Now mi[2][1] is non-zero
      fi;
      RECOG.DoRowOp_SL(mi,1,2,(std.one-mi[1][1])/mi[2][1],std);
  fi;
  # Now mi[1][1] is equal to one
  if not(IsZero(mi[2][1])) then
      RECOG.DoRowOp_SL(mi,2,1,-mi[2][1],std);
  fi;
  # Now mi[2][1] is equal to zero and thus mi[2][2] equal to one
  if not(IsZero(mi[1][2])) then
      RECOG.DoRowOp_SL(mi,1,2,-mi[1][2],std);
  fi;
  # Now mi is the identity matrix, the element collected in std
  # is the one to multiply on the left hand side to transform mi to the
  # identity. Thus it is equal to m.
  return SLPOfElm(std.left);
end;

RECOG.ExpressInStd_SL := function(m,std)
  # m a matrix, std a fake standard generator record with trivial
  # generators with memory
  local d,i,j,mi,pos;

  if IsObjWithMemory(m) then
      mi := InverseMutable(StripMemory(m));
  else
      mi := InverseMutable(m);
  fi;
  std.left := std.One;
  d := Length(m);
  for i in [1..d] do
      if not(IsOne(mi[i][i])) then
          pos := First([i+1..d],k->not IsZero(mi[k][i]));
          if pos = fail then
              if i = 1 then
                  pos := 2;
              else
                  pos := 1;
              fi;
              RECOG.DoRowOp_SL(mi,pos,i,std.one,std);
          fi;
          RECOG.DoRowOp_SL(mi,i,pos,(std.one-mi[i][i])/mi[pos][i],std);
      fi;
      # Now mi[i][i] is equal to one
      for j in Concatenation([1..i-1],[i+1..d]) do
          if not(IsZero(mi[j][i])) then
              RECOG.DoRowOp_SL(mi,j,i,mi[j][i],std);
          fi;
      od;
      # Now mi[i][i] is the only non-zero entry in the column
  od;
  # Now mi is the identity matrix, the element collected in std
  # is the one to multiply on the left hand side to transform mi to the
  # identity. Thus it is equal to m.
  return SLPOfElm(std.left);
end;


RECOG.FindStdGens_SL_EvenChar := function(sld,f)
  # gens of sld must be gens for SL(d,q) in its natural rep with memory
  # This function calls RECOG.SL_Even_constructdata and then extends 
  # the basis to a basis of the full row space and returns an slp such
  # that the SL(d,q) standard generators with respect to this basis are
  # expressed by the slp in terms of the original generators of sld.
local V,b,bas,basi,basit,d,data,diffv,diffw,el,ext,fakegens,gens,i,id,lambda,mu,n,notinv,nu,nu2,oldyf,oldyy,p,pos,q,resl2,sl2,sl2gens,sl2gensf,sl2genss,sl2stdf,slp,slpsl2std,slptosl2,st,std,stdsl2,w,x,xf,y,y2f,y3f,yf,yy,yy2,yy3,z,zf;

  # Some setup:
  p := Characteristic(f);
  q := Size(f);
  ext := DegreeOverPrimeField(f);
  d := DimensionOfMatrixGroup(sld);

  # First find an SL2 with the space it acts on:
  Print("Finding an SL2...\c");
  data := RECOG.SL_Even_constructdata(sld,q);
  Print("done.\n");
  bas := ShallowCopy(BasisVectors(Basis(data[2])));
  sl2 := data[1];
  slptosl2 := SLPOfElms(GeneratorsOfGroup(sl2));

  # Now compute the natural SL2 action and run constructive recognition:
  Print("Recognising this SL2 constructively in 2 dimensions...\c");
  sl2gens := StripMemory(GeneratorsOfGroup(sl2));
  V := VectorSpace(f,bas);
  b := Basis(V,bas);
  sl2genss := List(sl2gens,x->List(BasisVectors(b),v->Coefficients(b,v*x)));
  sl2genss := GeneratorsWithMemory(sl2genss);
  resl2 := RECOG.RecogniseSL2NaturalEvenChar(Group(sl2genss),f,false);
  Print("done.\n");
  slpsl2std := SLPOfElms(resl2.all);
  bas := resl2.bas * bas;
  # We need the actual transvections:
  slp := SLPOfElms([resl2.s[1],resl2.t[1]]);
  st := ResultOfStraightLineProgram(slp,StripMemory(GeneratorsOfGroup(sl2)));
  
  # Extend basis by something invariant under SL2:
  id := IdentityMat(d,f);
  nu := NullspaceMat(StripMemory(st[1]+id));
  nu2 := NullspaceMat(StripMemory(st[2]+id));
  Append(bas,SumIntersectionMat(nu,nu2)[2]);
  basi := bas^-1;
  basit := TransposedMatMutable(basi);

  # Now set up fake generators for keeping track what we do:
  fakegens := ListWithIdenticalEntries(Length(GeneratorsOfGroup(sld)),());
  fakegens := GeneratorsWithMemory(fakegens);
  sl2gensf := ResultOfStraightLineProgram(slptosl2,fakegens);
  sl2stdf := ResultOfStraightLineProgram(slpsl2std,sl2gensf);
  std := RECOG.InitSLstd(f,d,sl2stdf{[1..ext]},sl2stdf{[ext+1..2*ext]},
                         sl2stdf[2*ext+1],sl2stdf[2*ext+2]);

  for n in [2..d-1] do
      Print(n," \c");
      while true do   # will be left by break at the end
          x := PseudoRandom(sld);
          slp := SLPOfElm(x);
          xf := ResultOfStraightLineProgram(slp,fakegens);
          # From now on plain matrices, we have to keep track with the 
          # fake ones!
          x := StripMemory(x);

          # Find a new basis vector:
          y := st[1]^x;
          notinv := First([1..n],i->bas[i]*y<>bas[i]);
          if notinv = fail then continue; fi;  # try next x
          w := bas[notinv]*y-bas[notinv];
          if ForAll(basit{[n+1..d]},v->IsZero(ScalarProduct(v,w))) then
              continue;   # try next x
          fi;
          # Now make it so that w is invariant under SL_n by modifying
          # it by something in the span of bas{[1..n]}:
          for i in [1..n] do
              w := w - bas[i] * ScalarProduct(w,basit[i]);
          od;
          if w*y=w then Print("!\c"); continue; fi;

          # w is supposed to become the next basis vector number n+1.
          # So we need to throw away one of bas{[n+1..d]}:
          i := First([n+1..d],i->not(IsZero(ScalarProduct(w,basit[i]))));
          Remove(bas,i);
          Add(bas,w,n+1);
          # However, we want that the rest of them bas{[n+2..d]} is invariant
          # under y which we can achieve by adding a multiple of w:
          diffw := w*y-w;
          pos := PositionNonZero(diffw);
          for i in [n+2..d] do
              diffv := bas[i]*y-bas[i];
              if not(IsZero(diffv)) then
                  bas[i] := bas[i] - (diffv[pos]/diffw[pos]) * w;
              fi;
          od;
          basi := bas^-1;
          basit := TransposedMat(basi);
          # FIXME: This should be done more efficiently!

          # Compute the action of y-One(y) on Span(bas{[1..n+1]})
          yy := EmptyPlist(n+1);
          for i in [1..n+1] do
              Add(yy,(bas[i]*y-bas[i])*basi);
              yy[i] := yy[i]{[1..n+1]};
          od;
          if IsOne(yy[n+1][n+1]) then Print("#\c"); continue; fi;
          break;
      od;
      yf := xf^-1*std.s[1]*xf;

      # make sure that rows n-1 and n are non-zero:
      std.left := std.One;
      std.right := std.One;
      if IsZero(yy[n-1]) then
          RECOG.DoRowOp_SL(yy,n-1,notinv,std.one,std);
          RECOG.DoColOp_SL(yy,n-1,notinv,std.one,std);
      fi;
      if IsZero(yy[n]) then
          RECOG.DoRowOp_SL(yy,n,notinv,std.one,std);
          RECOG.DoColOp_SL(yy,n,notinv,std.one,std);
      fi;
      yf := std.left * yf * std.right;

      oldyy := MutableCopyMat(yy);
      oldyf := yf;

      while true do   # will be left by break when we had success!
          # Note that by construction yy[n][n+1] is not zero!
          yy2 := MutableCopyMat(yy);
          std.left := std.One;
          std.right := std.One;
          # We want to be careful not to kill row n:
          repeat
              lambda := PrimitiveRoot(f)^Random(0,q-1);
          until lambda <> yy2[n][n+1]/yy2[n-1][n+1];
          RECOG.DoRowOp_SL(yy2,n,n-1,lambda,std);
          RECOG.DoColOp_SL(yy2,n,n-1,lambda,std);
          mu := lambda;
          y2f := std.left * yf * std.right;

          yy3 := MutableCopyMat(yy);
          std.left := std.One;
          std.right := std.One;
          # We want to be careful not to kill row n:
          repeat
              lambda := PrimitiveRoot(f)^Random(0,q-1);
          until lambda <> yy3[n][n+1]/yy3[n-1][n+1] and lambda <> mu;
          RECOG.DoRowOp_SL(yy3,n,n-1,lambda,std);
          RECOG.DoColOp_SL(yy3,n,n-1,lambda,std);
          y3f := std.left * yf * std.right;

          # We now perform conjugations such that y leaves bas{[1..n-1]} fixed:
          # (remember that y+One(y) has rank 1 and does not fix bas[notinv])
          std.left := std.One;
          std.right := std.One;
          for i in [1..n-1] do
              lambda := -yy[i][n+1]/yy[n][n+1];
              RECOG.DoRowOp_SL(yy,i,n,lambda,std);
              RECOG.DoColOp_SL(yy,i,n,lambda,std);
          od;
          yf := std.left * yf * std.right;

          std.left := std.One;
          std.right := std.One;
          for i in [1..n-1] do
              lambda := -yy2[i][n+1]/yy2[n][n+1];
              RECOG.DoRowOp_SL(yy2,i,n,lambda,std);
              RECOG.DoColOp_SL(yy2,i,n,lambda,std);
          od;
          y2f := std.left * y2f * std.right;

          std.left := std.One;
          std.right := std.One;
          for i in [1..n-1] do
              lambda := -yy3[i][n+1]/yy3[n][n+1];
              RECOG.DoRowOp_SL(yy3,i,n,lambda,std);
              RECOG.DoColOp_SL(yy3,i,n,lambda,std);
          od;
          y3f := std.left * y3f * std.right;

          gens :=[ExtractSubMatrix(yy,[n,n+1],[n,n+1])+IdentityMat(2,f),
                  ExtractSubMatrix(yy2,[n,n+1],[n,n+1])+IdentityMat(2,f),
                  ExtractSubMatrix(yy3,[n,n+1],[n,n+1])+IdentityMat(2,f)];
          if RECOG.IsThisSL2Natural(gens,f) = true then break; fi;
          Print("$\c");
          yy := MutableCopyMat(oldyy);
          yf := oldyf;
      od;

      # Now perform a constructive recognition in the SL2 in the lower
      # right corner:
      gens := GeneratorsWithMemory(gens);
      resl2 := RECOG.RecogniseSL2NaturalEvenChar(Group(gens),f,gens[1]);
      stdsl2 := RECOG.InitSLfake(f,2);
      slp := RECOG.ExpressInStd_SL2(
               resl2.bas*Reversed(IdentityMat(2,f))*resl2.basi,stdsl2);
      el := ResultOfStraightLineProgram(slp,resl2.all);
      slp := SLPOfElm(el);
      # FIXME: this must be done more efficiently:
      z := ResultOfStraightLineProgram(slp,
                  [yy+One(yy),yy2+One(yy),yy3+One(yy)]);
      zf := ResultOfStraightLineProgram(slp,[yf,y2f,y3f]);

      std.left := std.One;
      std.right := std.One;
      # Now we clean out the last row of z:
      for i in [1..n-1] do
          if not(IsZero(z[n+1][i])) then
              RECOG.DoColOp_SL(z,n,i,z[n+1][i],std);
          fi;
      od;
      # Now we clean out the second last row of z:
      for i in [1..n-1] do
          if not(IsZero(z[n][i])) then
              RECOG.DoRowOp_SL(z,n,i,z[n][i],std);
          fi;
      od;
      zf := std.left * zf * std.right;

      # Now change the standard generators in the fakes:
      std.a := std.a * zf;
      std.b := std.b * zf;
      std.all[std.ext*2+1] := std.a;
      std.all[std.ext*2+2] := std.b;
      RECOG.ResetSLstd(std);

  od;
  Print("done.\n");
  return rec( slpstd := SLPOfElms(std.all), bas := bas, basi := basi );
end;

  
RECOG.RecogniseSL2NaturalEvenChar := function(g,f,torig)
  # f a finite field, g equal to SL(2,Size(f)), t either an element
  # of order p = Characteristic(f) or false.
  # Returns a set of standard generators for SL_2 and the base change
  # to expose it. Works with memory. Uses PseudoRandom.
  local a,actpos,am,b,bas,bm,c,can,ch,cm,co,co2,ext,el,ev,eva,evb,evbi,
        gens,i,j,k,kk,mas,masi,mat,mati,mb,o,one,os,p,pos,q,res,ss,ssm,t,tb,
        tm,tt,ttm,u,v,x,xb,xm;
  q := Size(f);
  p := Characteristic(f);
  ext := DegreeOverPrimeField(f);
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
          fi;
      until not(IsOne(tm));
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
  while Length(tt) < ext do
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
  while Length(ss) < ext do
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

  # Now we replace all the s and the t by some products to get rid
  # of the base changes:
  s := EmptyPlist(ext);
  t := EmptyPlist(ext);
  for i in [1..ext] do
      co := Positions(masi[i],Z(2));
      Add(s,Product(ssm{co}));
      co := Positions(mati[i],Z(2));
      Add(t,Product(ttm{co}));
  od;

  res :=  rec( g := g, t := t, s := s, bas := bas, basi := bas^-1,
              one := One(f), a := s[1]*t[1]*s[1], b := One(s[1]),
              One := One(s[1]), f := f, q := q, p := p, ext := ext,
              d := 2 );
  res.all := Concatenation(res.s,res.t,[res.a],[res.b]);
  return res;
end;

RECOG.GuessSL2ElmOrder := function(x,q)
  local facts,i,j,o,p,r,s,y,z;
  if IsOne(x) then return 1;
  elif IsOne(x^2) then return 2;
  fi;
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

RECOG.IsThisSL2Natural := function(gens,f)
  # Checks quickly whether or not this is SL(2,f).
  # The answer is not guaranteed to be correct, this is Las Vegas.
  local CheckElm,a,b,clos,coms,i,isabelian,j,l,notA5,q,seenqm1,seenqp1,x;

  CheckElm := function(x)
      local o;
      o := RECOG.GuessSL2ElmOrder(x,q);
      if o in [1,2] then return false; fi;
      if o > 5 then 
          if notA5 = false then Info(InfoRecog,4,"SL2: Group is not A5"); fi;
          notA5 := true; 
      fi;
      if (q+1) mod o = 0 then
          Info(InfoRecog,4,"SL2: Found element of order dividing q+1.");
          seenqp1 := true;
          if seenqm1 then return true; fi;
      else
          Info(InfoRecog,4,"SL2: Found element of order dividing q-1.");
          seenqm1 := true;
          if seenqp1 then return true; fi;
      fi;
      return false;
  end;

  if Length(gens) <= 1 then 
      Info(InfoRecog,4,"SL2: Group cyclic");
      return false; 
  fi;

  q := Size(f);
  seenqp1 := false;
  seenqm1 := false;
  notA5 := false;

  for i in [1..Length(gens)] do
      if CheckElm(gens[i]) then return true; fi;
  od;
  CheckElm(gens[1]*gens[2]);
  if Length(gens) >= 3 then
      CheckElm(gens[1]*gens[3]);
      CheckElm(gens[2]*gens[3]);
  fi;

  # First we check the derived group:
  coms := EmptyPlist(20);
  l := Length(gens);
  if l <= 4 then
      Info(InfoRecog,4,"SL2: Computing commutators of gens...");
      for i in [1..l-1] do
          for j in [i+1..l] do
              x := Comm(gens[i],gens[j]);
              if CheckElm(x) then return true; fi;
              Add(coms,x);
          od;
      od;
  else
      Info(InfoRecog,4,"SL2: Computing 6 random commutators...");
      for i in [1..6] do
          a := RandomSubproduct(gens);
          b := RandomSubproduct(gens);
          x := Comm(a,b);
          if CheckElm(x) then return true; fi;
          Add(coms,x);
      od;
  fi;
  if ForAll(coms,c->RECOG.IsScalarMat(c) <> false) then 
      Info(InfoRecog,4,"SL2: Group is soluble, commutators are central");
      return false; 
  fi;
  Info(InfoRecog,4,"SL2: Computing normal closure...");
  clos := FastNormalClosure(gens,coms,5);
  for i in [Length(coms)+1..Length(clos)] do
      if CheckElm(clos[i]) then return true; fi;
  od;
  if ForAll(clos{[Length(coms)+1..Length(clos)]},
            c->RECOG.IsScalarMat(c) <> false) then 
      Info(InfoRecog,4,"SL2: Group is soluble, derived subgroup central");
      return false; 
  fi;
  Info(InfoRecog,4,"SL2: Computing 6 random commutators...");
  isabelian := true;
  for i in [1..6] do
      a := RandomSubproduct(clos);
      b := RandomSubproduct(clos);
      x := Comm(a,b);
      if not(IsOne(x)) then isabelian := false; break; fi;
  od;
  if isabelian then 
      Info(InfoRecog,4,"SL2: Group is soluble, derived subgroup abelian");
      return false; 
  fi;

  # Now we know that the group is not dihedral!
  if notA5 then return true; fi;
  return false;
end;
