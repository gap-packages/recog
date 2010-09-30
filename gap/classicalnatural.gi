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

RECOG.RelativePrimeToqm1Part := function(q,n)
  local x,y;
  x := (q^n-1)/(q-1);
  repeat
      y := x/(q-1);
      x := NumeratorRat(y);
  until DenominatorRat(y) = q-1;
  return x;
end;

RECOG.SearchForElByCharPolFacts := function(g,f,degs,limit)
  local count,degrees,factors,pol,y;
  count := 0;
  while true do   # will be left by return
    if InfoLevel(InfoRecog) >= 3 then Print(".\c"); fi;
    y:=PseudoRandom(g);
    pol:=CharacteristicPolynomial(f,f,StripMemory(y),1);
    factors:=Factors(PolynomialRing(f),pol);
    degrees:=List(factors,Degree);
    SortParallel(degrees,factors);
    if degrees = degs then
      if InfoLevel(InfoRecog) >= 3 then Print("\n"); fi;
      return rec( el := y, factors := factors, degrees := degrees );
    fi;
    count := count + 1;
    if count >= limit then return fail; fi;
  od;
end;
  
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

RECOG.SL_FindSL2 := function(g,f)
  local V,a,bas,c,count,ev,gens,genss,genssm,gl4,h,i,j,n,ns,o,pos,pow,pr,q,r,
        res,sl2gens,sl3,slp,std,v,w,y,z,zz;
  q := Size(f);
  n := DimensionOfMatrixGroup(g);
  if q = 2 then
      # We look for a transvection:
      while true do   # will be left by break
          r := RECOG.SearchForElByCharPolFacts(g,f,[1,1,n-2],3*n+20);
          if r = fail then return fail; fi;
          y := r.el^(q^(n-2)-1);
          if not IsOne(y) and IsOne(y^2) then break; fi;
      od;
      # Find a good random conjugate:
      repeat
          z := y^PseudoRandom(g);
      until Order(z*y) = 3;
      gens := [y,z];
      o := IdentityMat(n,f);
      w := [];
      for i in [1..2] do
          for j in [1..n] do
              w[i] := o[j]*gens[i]-o[j];
              if not(IsZero(w[i])) then break; fi;
          od;
      od;
      return [Group(gens),VectorSpace(GF(q),w)];
  fi;
  if q = 3 and n = 3 then
      std := RECOG.MakeSL_StdGens(3,1,2,3);
      slp := RECOG.FindStdGensUsingBSGS(g,Concatenation(std.s,std.t),
                                        false,true);
      if slp = fail then return fail; fi;
      h := Group(ResultOfStraightLineProgram(slp,GeneratorsOfGroup(g)));
      o := IdentityMat(3,f);
      return [h,VectorSpace(f,o{[1..2]})];
  fi;
  if q = 3 and n = 4 then
      std := RECOG.MakeSL_StdGens(3,1,2,4);
      slp := RECOG.FindStdGensUsingBSGS(g,Concatenation(std.s,std.t),
                                        false,true);
      if slp = fail then return fail; fi;
      h := Group(ResultOfStraightLineProgram(slp,GeneratorsOfGroup(g)));
      o := IdentityMat(4,f);
      return [h,VectorSpace(f,o{[1..2]})];
  fi;
  if q = 3 then
      # We look for a transvection:
      while true do   # will be left by break
          r := RECOG.SearchForElByCharPolFacts(g,f,[1,1,n-2],3*n+20);
          if r = fail then return fail; fi;
          y := r.el^(q^(n-2)-1);
          if not IsOne(y) and IsOne(y^3) then break; fi;
      od;
      # Find a two good random conjugates:
      while true do   # will be left by return
          z := y^PseudoRandom(g);
          zz := y^PseudoRandom(g);
          gens := [y,z,zz];
          o := IdentityMat(n,f);
          ns := [];
          for j in [1..3] do
              for i in [1..n] do
                  w := o[i]*gens[j]-o[i];
                  if not(IsZero(w)) then break; fi;
              od;
              # Since y has order y at least one basis vector is moved.
              ns[j] := w;
          od;
          V := VectorSpace(f,ns);
          bas := Basis(V,ns);
          genss := List(StripMemory(gens),
                        x->List(ns,i->Coefficients(bas,i*x)));
          genssm := GeneratorsWithMemory(genss);
          sl3 := Group(genssm);
          pr := ProductReplacer(genssm,rec( maxdepth := 400, scramble := 0,
                                            scramblefactor := 0 ) );
          sl3!.pseudorandomfunc := [rec(func := Next,args := [pr])];
          res := RECOG.SL_FindSL2(sl3,f);
          if res = fail then 
              if InfoLevel(InfoRecog) >= 3 then Print("#\c"); fi;
              continue;
          fi;
          slp := SLPOfElms(GeneratorsOfGroup(res[1]));
          sl2gens := ResultOfStraightLineProgram(slp,gens);
          ns := BasisVectors(Basis(res[2])) * ns;
          ConvertToMatrixRep(ns,q);
          return [Group(sl2gens),VectorSpace(f,ns)];
      od;
  fi;
  if q = 4 and n = 3 then
      std := RECOG.MakeSL_StdGens(2,2,2,3);
      slp := RECOG.FindStdGensUsingBSGS(g,Concatenation(std.s,std.t),
                                        false,true);
      if slp = fail then return fail; fi;
      h := Group(ResultOfStraightLineProgram(slp,GeneratorsOfGroup(g)));
      o := IdentityMat(3,f);
      return [h,VectorSpace(f,o{[1..2]})];
  fi;
  if q = 5 and n = 4 then
      std := RECOG.MakeSL_StdGens(5,1,2,4);
      slp := RECOG.FindStdGensUsingBSGS(g,Concatenation(std.s,std.t),
                                        false,true);
      if slp = fail then return fail; fi;
      h := Group(ResultOfStraightLineProgram(slp,GeneratorsOfGroup(g)));
      o := IdentityMat(4,f);
      return [h,VectorSpace(f,o{[1..2]})];
  fi;
  if n mod (q-1) <> 0 and q <> 3 then   # The generic case:
      # We look for an element with n-1 dimensional eigenspace:
      count := 0;
      while true do    # will be left by break
          count := count + 1;
          if count > 20 then return fail; fi;
          r := RECOG.SearchForElByCharPolFacts(g,f,[1,n-1],3*n+20);
          if r = fail then return fail; fi;
          pow := RECOG.RelativePrimeToqm1Part(q,n-1);
          y := r.el^pow;
          o := Order(y);
          if o mod (q-1) = 0 then 
              y := y^(o/(q-1));
              break;
          fi;
      od;
      # Now y has order q-1 and and n-1 dimensional eigenspace
      ev := -Value(r.factors[1],0*Z(q));
      ns := NullspaceMat(StripMemory(r.el)-ev*StripMemory(One(y)));
      # this is a 1xn matrix now
      ns := ns[1];
      pos := PositionNonZero(ns);
      ns := (ns[pos]^-1) * ns;
      count := 0;
      while true do   # will be left by break
          count := count + 1;
          if count > 20 then return fail; fi;
          a := PseudoRandom(g);
          v := OnLines(ns,a);
          z := y^a;
          if OnLines(v,y) <> v and OnLines(ns,z) <> ns then
              # Now y and z most probably generate a GL(2,q), we need 
              # the derived subgroup and then check:
              c := Comm(y,z);
              sl2gens := FastNormalClosure([y,z],[c],1);
              V := VectorSpace(f,[ns,v]);
              bas := Basis(V,[ns,v]);
              genss := List(sl2gens,x->List([ns,v],i->Coefficients(bas,i*x)));
              if RECOG.IsThisSL2Natural(genss,f) then break; fi;
              if InfoLevel(InfoRecog) >= 3 then Print("$\c"); fi;
          else
              if InfoLevel(InfoRecog) >= 3 then Print("-\c"); fi;
          fi;
      od;
      if InfoLevel(InfoRecog) >= 3 then Print("\n"); fi;
      return [Group(sl2gens),VectorSpace(f,[ns,v])];
  fi;
  # Now q-1 does divide n, we have to do something else:
  # We look for an element with n-2 dimensional eigenspace:
  while true do    # will be left by break
      r := RECOG.SearchForElByCharPolFacts(g,f,[1,1,n-2],5*n+20);
      if r = fail then return fail; fi;
      pow := RECOG.RelativePrimeToqm1Part(q,n-2);
      y := r.el^pow;
      o := Order(y);
      if o mod (q-1) = 0 then 
          y := y^(o/(q-1));
          if RECOG.IsScalarMat(y) = false then break; fi;
      fi;
  od;
  # Now y has order q-1 and n-2 dimensional eigenspace
  if r.factors[1] <> r.factors[2] then
      ev := -Value(r.factors[1],0*Z(q));
      ns := NullspaceMat(StripMemory(r.el)-ev*StripMemory(One(y)));
      if not(IsMutable(ns)) then ns := MutableCopyMat(ns); fi;
      # this is a 1xn matrix now
      ev := -Value(r.factors[2],0*Z(q));
      Append(ns,NullspaceMat(StripMemory(r.el)-ev*StripMemory(One(y))));
      # ns now is a 2xn matrix
  else
      ev := -Value(r.factors[1],0*Z(q));
      ns := NullspaceMat((StripMemory(r.el)
                                     -ev*StripMemory(One(y)))^2);
      if not(IsMutable(ns)) then ns := MutableCopyMat(ns); fi;
  fi;

  count := 0;
  while true do   # will be left by break
      count := count + 1;
      if count > 20 then return fail; fi;
      if Length(ns) > 2 then ns := ns{[1..2]}; fi;
      a := PseudoRandom(g);
      Append(ns,ns * a);
      if RankMat(ns) < 4 then
          if InfoLevel(InfoRecog) >= 3 then Print("+\c"); fi;
          continue;
      fi;
      z := y^a;
      # Now y and z most probably generate a GL(4,q), we need 
      # the derived subgroup and then check:
      V := VectorSpace(f,ns);
      bas := Basis(V,ns);
      genss := List([y,z],x->List(ns,i->Coefficients(bas,i*x)));
      genssm := GeneratorsWithMemory(genss);
      gl4 := Group(genssm);
      pr := ProductReplacer(genssm,rec( maxdepth := 400, scramble := 0,
                                        scramblefactor := 0 ) );
      gl4!.pseudorandomfunc := [rec(func := Next,args := [pr])];
      res := RECOG.SL_FindSL2(gl4,f);
      if res = fail then 
          if InfoLevel(InfoRecog) >= 3 then Print("#\c"); fi;
          continue;
      fi;
      slp := SLPOfElms(GeneratorsOfGroup(res[1]));
      sl2gens := ResultOfStraightLineProgram(slp,[y,z]);
      ns := BasisVectors(Basis(res[2])) * ns;
      return [Group(sl2gens),VectorSpace(f,ns)];
  od;
  return fail;
end;


RECOG.SL_Even_constructdata:=function(g,q)
local S,a,b,degrees,eva,factors,gens,h,i,n,ns,o,pol,pos,ready,ready2,
      ready3,subgplist,w,ww,y,yy,z;

n:=DimensionOfMatrixGroup(g);

if q=2 then
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
else
  #case of q <> 2
  repeat  
    ready:=false;
    y:=PseudoRandom(g);
    if InfoLevel(InfoRecog) >= 3 then Print(".\c"); fi;
    pol:=CharacteristicPolynomial(GF(q),GF(q),StripMemory(y),1);
    factors:=Factors(pol);
    degrees:=List(factors,Degree);
    if n-1 in degrees then
       yy := y^(RECOG.RelativePrimeToqm1Part(q,n-1));
       o := Order(yy);
       if o mod (q-1) = 0 then
           yy := yy^(o/(q-1));
           ready := true;
       fi;
    fi;
  until ready;
  if InfoLevel(InfoRecog) >= 3 then Print("\n"); fi;

  ready2:=false;
  ready3:=false;
  repeat
     gens:=[yy];
     a := PseudoRandom(g);
     b := PseudoRandom(g);
     Add(gens,yy^a);
     Add(gens,yy^b);
     h:=Group(gens);
     if q = 4 then
       S := StabilizerChain(h);
       if not(Size(S) in [60480,3*60480]) then continue; fi;
       pos := Position(degrees,1);
       eva := -Value(factors[pos],0*Z(q));
       ns := NullspaceMat(StripMemory(y)-eva*One(StripMemory(y)));
       return [h,
          VectorSpace(GF(q),[ns[1],ns[1]*StripMemory(a),ns[1]*StripMemory(b)])];
     fi;
      
     # Now check using ppd-elements:
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
  if IsObjWithMemory(GeneratorsOfGroup(g)[1]) then
      gm := GroupWithMemory(StripMemory(GeneratorsOfGroup(g)));
  else
      gm := GroupWithMemory(g);
  fi;
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
          new := std.s[k]^coeffs[k] * new;
          if j > i+1 then new := Getbj(j-i-1) * new; fi;
          if i > 1 then new := Getai(i-1) * new; fi;
      elif i > j then
          # We need to multiply from the left with the element
          #    a^(j-1) * b^(i-j-1) * t_k * b^-(i-j-1) * a^-(j-1)
          # from the left.
          if j > 1 then new := Getai(j-1)^-1 * new; fi;
          if i > j+1 then new := Getbj(i-j-1)^-1 * new; fi;
          new := std.t[k]^coeffs[k] * new;
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
          new := std.s[k]^coeffs[k] * new;
          if j > i+1 then new := Getbj(j-i-1) * new; fi;
          if i > 1 then new := Getai(i-1) * new; fi;
      elif i > j then
          # We need to multiply from the right with the element
          #    a^(j-1) * b^(i-j-1) * t_k * b^-(i-j-1) * a^-(j-1)
          # from the left.
          if j > 1 then new := Getai(j-1)^-1 * new; fi;
          if i > j+1 then new := Getbj(i-j-1)^-1 * new; fi;
          new := std.t[k]^coeffs[k] * new;
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
  if IsEvenInt(n) then
      a[1] := -a[1];
  else
      b[2] := -b[2];
  fi;
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
              pos := i+1;
              RECOG.DoRowOp_SL(mi,pos,i,std.one,std);
          fi;
          RECOG.DoRowOp_SL(mi,i,pos,(std.one-mi[i][i])/mi[pos][i],std);
      fi;
      # Now mi[i][i] is equal to one
      for j in Concatenation([1..i-1],[i+1..d]) do
          if not(IsZero(mi[j][i])) then
              RECOG.DoRowOp_SL(mi,j,i,-mi[j][i],std);
          fi;
      od;
      # Now mi[i][i] is the only non-zero entry in the column
  od;
  # Now mi is the identity matrix, the element collected in std
  # is the one to multiply on the left hand side to transform mi to the
  # identity. Thus it is equal to m.
  return SLPOfElm(std.left);
end;

InstallOtherMethod( \*, "for two funny product objects",
  [ IsFunnyProductObject, IsFunnyProductObject ],
  function(a,b)
    return Objectify(FunnyProductObjsType,[a![1]+a![2]*b![1],a![2]*b![2]]);
  end );

InstallOtherMethod( InverseSameMutability, "for a funny product object",
  [ IsFunnyProductObject ],
  function(a)
    local i;
    i := a![2]^-1;
    return Objectify(FunnyProductObjsType,[-i*a![1],i]);
  end );

InstallOtherMethod( OneMutable, "for a funny product object",
  [ IsFunnyProductObject ],
  function(a)
    return Objectify(FunnyProductObjsType,[Zero(a![1]),OneMutable(a![2])]);
  end );

InstallMethod( FunnyProductObj, "for two arbitrary objects",
  [ IsObject, IsObject ],
  function(a,b)
    return Objectify(FunnyProductObjsType,[a,b]);
  end );

RECOG.FindStdGens_SL_EvenChar := function(sld,f)
  # gens of sld must be gens for SL(d,q) in its natural rep with memory
  # This function calls RECOG.SL_Even_constructdata and then extends 
  # the basis to a basis of the full row space and returns an slp such
  # that the SL(d,q) standard generators with respect to this basis are
  # expressed by the slp in terms of the original generators of sld.
  local V,b,bas,basi,basit,d,data,diffv,diffw,el,ext,fakegens,gens,i,id,
        lambda,mu,n,notinv,nu,nu2,oldyf,oldyy,p,pos,q,resl2,sl2,sl2gens,
        sl2gensf,sl2genss,sl2stdf,slp,slpsl2std,slptosl2,st,std,stdsl2,
        w,x,xf,y,y2f,y3f,yf,yy,yy2,yy3,yyy,yyy2,yyy3,z,zf,zzz,goodguy;

  # Some setup:
  p := Characteristic(f);
  q := Size(f);
  ext := DegreeOverPrimeField(f);
  d := DimensionOfMatrixGroup(sld);
  if not(IsObjWithMemory(GeneratorsOfGroup(sld)[1])) then
      sld := GroupWithMemory(sld);
  fi;

  # First find an SL2 with the space it acts on:
  Info(InfoRecog,2,"Finding an SL2...");
  #data := RECOG.SL_Even_constructdata(sld,q);
  repeat
      data := RECOG.SL_FindSL2(sld,f);
  until data <> fail;
  bas := ShallowCopy(BasisVectors(Basis(data[2])));
  sl2 := data[1];
  slptosl2 := SLPOfElms(GeneratorsOfGroup(sl2));

  # Now compute the natural SL2 action and run constructive recognition:
  sl2gens := StripMemory(GeneratorsOfGroup(sl2));
  V := VectorSpace(f,bas);
  b := Basis(V,bas);
  sl2genss := List(sl2gens,x->List(BasisVectors(b),v->Coefficients(b,v*x)));
  for i in sl2genss do ConvertToMatrixRep(i,q); od;
  Info(InfoRecog,2,
       "Recognising this SL2 constructively in 2 dimensions...");
  sl2genss := GeneratorsWithMemory(sl2genss);
  if IsEvenInt(q) then
      resl2 := RECOG.RecogniseSL2NaturalEvenChar(Group(sl2genss),f,false);
  else
      resl2 := RECOG.RecogniseSL2NaturalOddCharUsingBSGS(Group(sl2genss),f);
  fi;
  slpsl2std := SLPOfElms(resl2.all);
  bas := resl2.bas * bas;
  # We need the actual transvections:
  slp := SLPOfElms([resl2.s[1],resl2.t[1]]);
  st := ResultOfStraightLineProgram(slp,StripMemory(GeneratorsOfGroup(sl2)));
  
  # Extend basis by something invariant under SL2:
  id := IdentityMat(d,f);
  nu := NullspaceMat(StripMemory(st[1]-id));
  nu2 := NullspaceMat(StripMemory(st[2]-id));
  Append(bas,SumIntersectionMat(nu,nu2)[2]);
  ConvertToMatrixRep(bas,q);
  basi := bas^-1;
  basit := TransposedMatMutable(basi);

  # Now set up fake generators for keeping track what we do:
  fakegens := ListWithIdenticalEntries(Length(GeneratorsOfGroup(sld)),());
  fakegens := GeneratorsWithMemory(fakegens);
  sl2gensf := ResultOfStraightLineProgram(slptosl2,fakegens);
  sl2stdf := ResultOfStraightLineProgram(slpsl2std,sl2gensf);
  std := RECOG.InitSLstd(f,d,sl2stdf{[1..ext]},sl2stdf{[ext+1..2*ext]},
                         sl2stdf[2*ext+1],sl2stdf[2*ext+2]);

  workrec := rec( n := 2, slnstdf := sl2stdf, bas := bas, basi := basi,
                  std := std, sld := sld, sldf := fakegens, f := f );

Error("... now go on with alternative going up...");

  Info(InfoRecog,2,"Going up to SL_d again...");
  for n in [Dimension(data[2])..d-1] do
      if InfoLevel(InfoRecog) >= 3 then Print(n," \c"); fi;
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
          if w*y=w then 
              if InfoLevel(InfoRecog) >= 3 then Print("!\c"); fi;
              continue; 
          fi;

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

          # Compute the action of y-One(y) on Span(bas{[1..n+1]})
          yy := EmptyPlist(n+1);
          for i in [1..n+1] do
              Add(yy,(bas[i]*y-bas[i])*basi);
              yy[i] := yy[i]{[1..n+1]};
          od;
          if q > 2 and IsOne(yy[n+1][n+1]) then 
              if InfoLevel(InfoRecog) >= 3 then Print("#\c"); fi;
              continue; 
          fi;
          ConvertToMatrixRep(yy,q);
          break;
      od;
      yf := xf^-1*std.s[1]*xf;

      # make sure that rows n-1 and n are non-zero:
      std.left := std.One;
      std.right := std.One;
      if IsZero(yy[n-1]) then
          RECOG.DoRowOp_SL(yy,n-1,notinv,std.one,std);
          RECOG.DoColOp_SL(yy,n-1,notinv,-std.one,std);
      fi;
      if IsZero(yy[n]) then
          RECOG.DoRowOp_SL(yy,n,notinv,std.one,std);
          RECOG.DoColOp_SL(yy,n,notinv,-std.one,std);
      fi;
      yf := std.left * yf * std.right;

      oldyy := MutableCopyMat(yy);
      oldyf := yf;

      if q = 2 then
          # In this case y is already good after cleaning out!
          # (remember that y+One(y) has rank 1 and does not fix bas[notinv])
          std.left := std.One;
          std.right := std.One;
          for i in [1..n-1] do
              lambda := -yy[i][n+1]/yy[n][n+1];
              RECOG.DoRowOp_SL(yy,i,n,lambda,std);
              RECOG.DoColOp_SL(yy,i,n,-lambda,std);
          od;
          yf := std.left * yf * std.right;
          z := yy+One(yy);
          zf := yf;
          if not(IsZero(z[n][n])) or not(IsOne(z[n][n+1])) or
             not(IsZero(z[n+1][n+1])) or not(IsOne(z[n+1][n])) then
              Error("How on earth could this happen???");
          fi;
      else  # q > 2
          while true do   # will be left by break when we had success!
              # Note that by construction yy[n][n+1] is not zero!
              yy2 := MutableCopyMat(yy);
              std.left := std.One;
              std.right := std.One;
              # We want to be careful not to kill row n:
              repeat
                  lambda := PrimitiveRoot(f)^Random(0,q-1);
              until lambda <> -yy2[n][n+1]/yy2[n-1][n+1];
              RECOG.DoRowOp_SL(yy2,n,n-1,lambda,std);
              RECOG.DoColOp_SL(yy2,n,n-1,-lambda,std);
              mu := lambda;
              y2f := std.left * yf * std.right;

              yy3 := MutableCopyMat(yy);
              std.left := std.One;
              std.right := std.One;
              # We want to be careful not to kill row n:
              repeat
                  lambda := PrimitiveRoot(f)^Random(0,q-1);
              until (lambda <> -yy3[n][n+1]/yy3[n-1][n+1]) and 
                    (lambda <> mu or q = 3);   
                    # in GF(3) there are not enough values!
              RECOG.DoRowOp_SL(yy3,n,n-1,lambda,std);
              RECOG.DoColOp_SL(yy3,n,n-1,-lambda,std);
              y3f := std.left * yf * std.right;

              # We now perform conjugations such that the ys leave 
              # bas{[1..n-1]} fixed:

              # (remember that y-One(y) has rank 1 and does not fix bas[notinv])
              std.left := std.One;
              std.right := std.One;
              for i in [1..n-1] do
                  lambda := -yy[i][n+1]/yy[n][n+1];
                  RECOG.DoRowOp_SL(yy,i,n,lambda,std);
                  RECOG.DoColOp_SL(yy,i,n,-lambda,std);
              od;
              yf := std.left * yf * std.right;

              std.left := std.One;
              std.right := std.One;
              for i in [1..n-1] do
                  lambda := -yy2[i][n+1]/yy2[n][n+1];
                  RECOG.DoRowOp_SL(yy2,i,n,lambda,std);
                  RECOG.DoColOp_SL(yy2,i,n,-lambda,std);
              od;
              y2f := std.left * y2f * std.right;

              std.left := std.One;
              std.right := std.One;
              for i in [1..n-1] do
                  lambda := -yy3[i][n+1]/yy3[n][n+1];
                  RECOG.DoRowOp_SL(yy3,i,n,lambda,std);
                  RECOG.DoColOp_SL(yy3,i,n,-lambda,std);
              od;
              y3f := std.left * y3f * std.right;

              gens :=[ExtractSubMatrix(yy,[n,n+1],[n,n+1])+IdentityMat(2,f),
                      ExtractSubMatrix(yy2,[n,n+1],[n,n+1])+IdentityMat(2,f),
                      ExtractSubMatrix(yy3,[n,n+1],[n,n+1])+IdentityMat(2,f)];
              if RECOG.IsThisSL2Natural(gens,f) = true then break; fi;
              if InfoLevel(InfoRecog) >= 3 then Print("$\c"); fi;
              yy := MutableCopyMat(oldyy);
              yf := oldyf;
          od;

          # Now perform a constructive recognition in the SL2 in the lower
          # right corner:
          gens := GeneratorsWithMemory(gens);
          if IsEvenInt(q) then
              resl2 := RECOG.RecogniseSL2NaturalEvenChar(Group(gens),f,gens[1]);
          else
              resl2 := RECOG.RecogniseSL2NaturalOddCharUsingBSGS(Group(gens),f);
          fi;
          stdsl2 := RECOG.InitSLfake(f,2);
          goodguy := Reversed(IdentityMat(2,f));
          goodguy[1][2] := - goodguy[1][2];
          slp := RECOG.ExpressInStd_SL2(resl2.bas*goodguy*resl2.basi,stdsl2);
          el := ResultOfStraightLineProgram(slp,resl2.all);
          slp := SLPOfElm(el);

          yy := yy+One(yy);
          yy2 := yy2+One(yy2);
          yy3 := yy3+One(yy3);
          yyy := FunnyProductObj(ExtractSubMatrix(yy,[n,n+1],[1..n-1]),
                                 ExtractSubMatrix(yy,[n,n+1],[n,n+1]));
          yyy2 := FunnyProductObj(ExtractSubMatrix(yy2,[n,n+1],[1..n-1]),
                                  ExtractSubMatrix(yy2,[n,n+1],[n,n+1]));
          yyy3 := FunnyProductObj(ExtractSubMatrix(yy3,[n,n+1],[1..n-1]),
                                  ExtractSubMatrix(yy3,[n,n+1],[n,n+1]));
          zzz := ResultOfStraightLineProgram(slp,[yyy,yyy2,yyy3]);
          z := OneMutable(yy);
          CopySubMatrix(zzz![1],z,[1..2],[n,n+1],[1..n-1],[1..n-1]);
          CopySubMatrix(zzz![2],z,[1..2],[n,n+1],[1..2],[n,n+1]);
          zf := ResultOfStraightLineProgram(slp,[yf,y2f,y3f]);
      fi;

      std.left := std.One;
      std.right := std.One;
      # Now we clean out the last row of z:
      for i in [1..n-1] do
          if not(IsZero(z[n+1][i])) then
              RECOG.DoColOp_SL(z,n,i,-z[n+1][i],std);
          fi;
      od;
      # Now we clean out the second last row of z:
      for i in [1..n-1] do
          if not(IsZero(z[n][i])) then
              RECOG.DoRowOp_SL(z,n,i,-z[n][i],std);
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
  if InfoLevel(InfoRecog) >= 3 then Print(".\n"); fi;
  return rec( slpstd := SLPOfElms(std.all), bas := bas, basi := basi );
end;

RECOG.RecogniseSL2NaturalOddCharUsingBSGS := function(g,f)
  local ext,p,q,res,slp,std;
  p := Characteristic(f);
  ext := DegreeOverPrimeField(f);
  q := Size(f);
  std := RECOG.MakeSL_StdGens(p,ext,2,2);
  slp := RECOG.FindStdGensUsingBSGS(g,std.all,false,true);
  if slp = fail then return fail; fi;
  res := rec( g := g, one := One(f), One := One(g), f := f, q := q,
              p := p, ext := ext, d := 2, bas := IdentityMat(2,f),
              basi := IdentityMat(2,f) );
  res.all := ResultOfStraightLineProgram(slp,GeneratorsOfGroup(g));
  res.s := res.all{[1..ext]};
  res.t := res.all{[ext+1..2*ext]};
  res.a := res.all[2*ext+1];
  res.b := res.all[2*ext+2];
  return res;
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
  od;
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
  od;
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

RECOG.SL_DoubleDimension := function(sld,slnstd,d,n,f,bas,basi)
  local c,ext,p,pf,q,x,y;
  q := Size(f);
  p := Characteristic(f);
  ext := DegreeOverPrimeField(f);
  pf := GF(p);

  # First we need an element of sl_n with 1-dimensional fixed space in
  # the n-space:
  if p = 2 or IsOddInt(n) then
      y := slnstd.a;                 # the n-cycle does the job
  else
      y := slnstd.b * slnstd.s[1];   # this does it.
  fi;
  x := PseudoRandom(sld);
  c := y^x;

  # We hope that H := <slnstd> and H^c generate an SL_(2n-1)
end;

RECOG.GuessSL2ElmOrder := function(x,f)
  local facts,i,j,o,p,q,r,s,y,z;
  p := Characteristic(f);
  q := Size(f);
  if IsOne(x) then return 1;
  elif IsOne(x^2) then return 2;
  fi;
  if p > 2 then
      y := x^p;
      if IsOne(y) then return p;
      elif IsOddInt(p) and IsOne(y^2) then 
          return 2*p;
      fi;
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

RECOG.GuessProjSL2ElmOrder := function(x,f)
  local facts,i,j,o,p,q,r,s,y,z;
  p := Characteristic(f);
  q := Size(f);
  if IsOneProjective(x) then return 1;
  elif IsEvenInt(p) and IsOneProjective(x^2) then return 2;
  fi;
  if p > 2 then
      y := x^p;
      if IsOneProjective(y) then return p; fi;
  fi;
  if IsOneProjective(x^(q-1)) then
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
          if not(IsOneProjective(z)) then break; fi;
          j := j - 1;
      od;
      o := o * p[1]^(j+1);
  od;
  return o;
end;

RECOG.IsThisSL2Natural := function(gens,f)
  # Checks quickly whether or not this is SL(2,f).
  # The answer is not guaranteed to be correct, this is Las Vegas.
  local CheckElm,a,b,clos,coms,i,isabelian,j,l,notA5,p,q,S,seenqm1,seenqp1,x;

  CheckElm := function(x)
      local o;
      o := RECOG.GuessProjSL2ElmOrder(x,f);
      if o in [1,2] then return false; fi;
      if o > 5 then 
          if notA5 = false then Info(InfoRecog,4,"SL2: Group is not A5"); fi;
          notA5 := true; 
          if seenqp1 and seenqm1 then return true; fi;
      fi;
      if o = p or o <= 5 then return false; fi;
      if (q+1) mod o = 0 then
          if not(seenqp1) then
              Info(InfoRecog,4,"SL2: Found element of order dividing q+1.");
              seenqp1 := true;
              if seenqm1 and notA5 then return true; fi;
          fi;
      else
          if not(seenqm1) then 
              Info(InfoRecog,4,"SL2: Found element of order divising q-1.");
              seenqm1 := true; 
              if seenqp1 and notA5 then return true; fi;
          fi;
      fi;
      return false;
  end;

  if Length(gens) <= 1 then 
      Info(InfoRecog,4,"SL2: Group cyclic");
      return false; 
  fi;
  
  q := Size(f);
  p := Characteristic(f);
  if q <= 32 then    # this could be increased if needed
      Info(InfoRecog,4,"SL2: Computing stabiliser chain.");
      S := StabilizerChain(Group(gens));
      Info(InfoRecog,4,"SL2: size is ",Size(S));
      return Size(S) = q*(q-1)*(q+1);
  fi;

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
          a := RECOG.RandomSubproduct(gens,rec());
          b := RECOG.RandomSubproduct(gens,rec());
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
      a := RECOG.RandomSubproduct(clos,rec());
      b := RECOG.RandomSubproduct(clos,rec());
      x := Comm(a,b);
      if RECOG.IsScalarMat(x) = false then isabelian := false; break; fi;
  od;
  if isabelian then 
      Info(InfoRecog,4,
           "SL2: Group is soluble, derived subgroup abelian mod scalars");
      return false; 
  fi;

  # Now we know that the group is not dihedral!
  return false;
end;

SLPforElementFuncsProjective.PSL2 := function(ri,x)
  local det,log,slp,y,z;
  ri!.fakegens.count := ri!.fakegens.count + 1;
  if ri!.fakegens.count > 1000 then
      ri!.fakegens := RECOG.InitSLfake(ri!.field,2);
      ri!.fakegens.count := 0;
  fi;
  y := ri!.nicebas * x * ri!.nicebasi;
  det := DeterminantMat(y);
  if not(IsOne(det)) then
      z := PrimitiveRoot(ri!.field);
      log := LogFFE(det,z);
      y := y * z^(-log*ri!.gcd.coeff1/ri!.gcd.gcd);
  fi;
  slp := RECOG.ExpressInStd_SL2(y,ri!.fakegens);
  return slp;
end;

SLPforElementFuncsProjective.PSLdEven := function(ri,x)
  local det,log,slp,y,z;
  ri!.fakegens.count := ri!.fakegens.count + 1;
  if ri!.fakegens.count > 1000 then
      ri!.fakegens := RECOG.InitSLfake(ri!.field,ri!.dimension);
      ri!.fakegens.count := 0;
  fi;
  y := ri!.nicebas * x * ri!.nicebasi;
  det := DeterminantMat(y);
  if not(IsOne(det)) then
      z := PrimitiveRoot(ri!.field);
      log := LogFFE(det,z);
      y := y * z^(-log*ri!.gcd.coeff1/ri!.gcd.gcd);
  fi;
  slp := RECOG.ExpressInStd_SL(y,ri!.fakegens);
  return slp;
end;

FindHomMethodsProjective.ClassicalNatural := function(ri,g)
  local changed,classical,d,det,ext,f,gcd,gens,gg,gm,i,log,p,pr,q,std,stdg,z;
  d := ri!.dimension;
  f := ri!.field;
  q := Size(f);
  p := Characteristic(f);
  RECOG.SetPseudoRandomStamp(g,"ClassicalNatural");

  # First get rid of nasty determinants:
  gens := ShallowCopy(GeneratorsOfGroup(g));
  changed := false;
  z := Z(q);
  gcd := Gcdex(d,q-1);
  for i in [1..Length(gens)] do
      det := DeterminantMat(gens[i]);
      if not(IsOne(det)) then
          log := LogFFE(det,z);
          if log mod gcd.gcd <> 0 then Error("!!!"); fi;
          gens[i] := gens[i] * z^(-log*gcd.coeff1/gcd.gcd);
          changed := true;
      fi;
  od;
  if changed then
      gg := GroupWithGenerators(gens);
      gm := GroupWithMemory(gens);
      pr := ProductReplacer(GeneratorsOfGroup(gm),rec(maxdepth := 500));
      gm!.pseudorandomfunc := [rec( func := Next, args := [pr] )];
  else
      gg := g;
      gm := Group(ri!.gensHmem);
      gm!.pseudorandomfunc := [rec(func := function(ri,name,bool)
                                      return RandomElm(ri,name,bool).el;
                                    end,
                            args := [ri,"ClassicalNatural",true])];
  fi;

  if d = 2 then
      # We only have to check for (P)SL_2 since otherwise the subfield
      # method will detect it. Note that this is a projective method,
      # but a projective group contains PSL_2 if and only if the matrix
      # group generated by the same matrices (possibly scaled to make
      # the determinant to be 1) contains SL_2.
      if IsEvenInt(q) then
          if not(RECOG.IsThisSL2Natural(GeneratorsOfGroup(gg),f)) then
              Info(InfoRecog,2,"ClassicalNatural: Is not PSL.");
              return fail;
          fi;
          # OK, this is (P)SL2, lets set up the recognition:
          Info(InfoRecog,2,"ClassicalNatural: this is PSL_2!");
          std := RECOG.RecogniseSL2NaturalEvenChar(gm,f,false);
          Setslptonice(ri,SLPOfElms(std.all));
          ri!.nicebas := std.bas;
          ri!.nicebasi := std.basi;
          SetNiceGens(ri,List(StripMemory(std.all),x->std.basi*x*std.bas));
          ri!.fakegens := RECOG.InitSLfake(f,2);
          ri!.fakegens.count := 0;
          ri!.comment := "_PSL2Even";
          ri!.gcd := gcd;
          SetFilterObj(ri,IsLeaf);
          SetSize(ri,(q+1)*(q-1)*q);
          Setslpforelement(ri,SLPforElementFuncsProjective.PSL2);
          return true;
      else   # odd case
          if not(RECOG.IsThisSL2Natural(GeneratorsOfGroup(gg),f)) then
              Info(InfoRecog,2,"ClassicalNatural: Is not PSL.");
              return fail;
          fi;
          # OK, this is (P)SL2, lets set up the recognition:
          Info(InfoRecog,2,"ClassicalNatural: this is PSL_2!");
          std := RECOG.RecogniseSL2NaturalOddCharUsingBSGS(gm,f);
          Setslptonice(ri,SLPOfElms(std.all));
          ri!.nicebas := std.bas;
          ri!.nicebasi := std.basi;
          SetNiceGens(ri,List(StripMemory(std.all),x->std.basi*x*std.bas));
          ri!.fakegens := RECOG.InitSLfake(f,2);
          ri!.fakegens.count := 0;
          ri!.comment := "_PSL2Odd";
          ri!.gcd := gcd;
          SetFilterObj(ri,IsLeaf);
          SetSize(ri,(q+1)*(q-1)*q/Gcd(2,q-1));
          Setslpforelement(ri,SLPforElementFuncsProjective.PSL2);
          return true;
      fi;
  else   # bigger than 2:
      classical := RecogniseClassical(gg);
      if classical.IsSLContained = true then
          # Do not run the generic code in small cases:
          if (q^d-1)/(q-1) <= 1000 or q=5 then  
              # FIXME: We do not have a FindSL2 for this case!
              Info(InfoRecog,2,"Classical natural: SL(",d,",",q,"): small ",
                   "case, handing over to Schreier-Sims.");
              ri!.comment := Concatenation("_SL(",String(d),",",String(q),")",
                                           "_StabilizerChain");
              return FindHomMethodsProjective.StabilizerChain(ri,g);
          fi;
          Info(InfoRecog,2,"ClassicalNatural: this is PSL_n!");
          std := RECOG.FindStdGens_SL_EvenChar(gm,f);
          Setslptonice(ri,std.slpstd);
          ri!.nicebas := std.bas;
          ri!.nicebasi := std.basi;
          ext := DegreeOverPrimeField(f);
          stdg := RECOG.MakeSL_StdGens(p,ext,d,d);
          SetNiceGens(ri,List(StripMemory(stdg.all),
                      x->std.basi*x*std.bas));
          ri!.fakegens := RECOG.InitSLfake(f,d);
          ri!.fakegens.count := 0;
          ri!.comment := "_PSLdEven";
          ri!.gcd := gcd;
          SetFilterObj(ri,IsLeaf);
          SetSize(ri,Product([0..d-1],i->(q^d-q^i))/((q-1)*gcd.gcd));
          Setslpforelement(ri,SLPforElementFuncsProjective.PSLdEven);
          return true;
      else
          Info(InfoRecog,2,"ClassicalNatural: Is not PSL.");
      fi;
      return fail;
  fi;

end;

##
##  This program is free software: you can redistribute it and/or modify
##  it under the terms of the GNU General Public License as published by
##  the Free Software Foundation, either version 3 of the License, or
##  (at your option) any later version.
##
##  This program is distributed in the hope that it will be useful,
##  but WITHOUT ANY WARRANTY; without even the implied warranty of
##  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
##  GNU General Public License for more details.
##
##  You should have received a copy of the GNU General Public License
##  along with this program.  If not, see <http://www.gnu.org/licenses/>.
##

