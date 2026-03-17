#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This files's authors include Max Neunhöffer, Ákos Seress.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
##
##  Constructive recognition of classical groups in their natural
##  representation.
##
#############################################################################

InstallMethod( CharacteristicPolynomial, "for a memory element matrix",
  [ IsMatrix and IsObjWithMemory ],
  function(m)
    return CharacteristicPolynomial(m!.el);
  end );

InstallOtherMethod( \-, "for two memory elements",
  [ IsMatrix and IsObjWithMemory, IsMatrix and IsObjWithMemory ],
  function(m,n)
    return m!.el - n!.el;
  end );

InstallMethod( Eigenspaces, "for a field and a memory element matrix",
  [ IsField, IsMatrix and IsObjWithMemory ],
  function( f, m )
    return Eigenspaces(f,m!.el);
  end );

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
      if not l[i].isone then
          return fail;
      fi;
      Add(gens,ResultOfStraightLineProgram(l[i].slp,strong));
  od;
  return SLPOfElms(gens);
end;

RECOG.ResetSLstd := function(r)
  r.left := One(r.a);
  r.right := One(r.a);
  if not IsBound(r.cache) then
      r.cache := [EmptyPlist(100),EmptyPlist(100),
                  List([1..r.ext],i->[]),     # rowopcache
                  List([1..r.ext],i->[])];    # colopcache
  fi;
  return r;
end;

# TODO: document the parameters
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

# TODO: document this; what does "fake" mean????
# Theory: the fake gens are only used for their memory. Since we are only
# interested in the memory (to produce slps), we use trivial permutations for
# the underlying group elements, so that the multiplication is cheap.
# Verify and then document this.
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
  #   a : e_n -> e_{n-1} -> ... -> e_1 -> (-1)^(n+1) e_n
  #   b : e_n -> e_{n-1} -> ... -> e_2 -> (-1)^n e_n and e_1 -> e_1
  #   s : e_1 -> e_1+ * e_2, e_i -> e_i   for i > 1
  #   t : e_2 -> e_1+ * e_2, e_i -> e_i   for i <> 2
  # s and t are lists of length ext to span over GF(p) all the scalars
  # in *.
  # Note that V_i = <e_1,...,e_i>.
  # So <s,t> is an SL_2 in the upper left corner, a is an n-cycle
  # b is an n-1 cycle with garbage fixing the first vector
  # This only modifies the record std collecting a straight line program.
  local Getai,Getbj,coeffs,k,new,newnew;

  Getai := function(l)
      local pos;
      if l < 0 then pos := std.d - l;
               else pos := l;
      fi;
      if not IsBound(std.cache[1][pos]) then
          std.cache[1][pos] := std.a^l;
      fi;
      return std.cache[1][pos];
  end;
  Getbj := function(l)
      local pos;
      if l < 0 then pos := std.d - l;
               else pos := l;
      fi;
      if not IsBound(std.cache[2][pos]) then
          std.cache[2][pos] := std.b^l;
      fi;
      return std.cache[2][pos];
  end;

  newnew := std.One;
  coeffs := RECOG.FindFFCoeffs(std,lambda);
  for k in [1..std.ext] do
      if not IsZero(coeffs[k]) then
          if IsBound(std.cache[3][k][i]) and
             IsBound(std.cache[3][k][i][j]) then
              new := std.cache[3][k][i][j];
          else;
              new := std.One;
              if i < j then
                  # We need to multiply from the left with the element
                  #    a^(i-1) * b^(j-i-1) * s_k * b^-(j-i-1) * a^-(i-1)
                  # from the left.
                  if i > 1 then new := Getai(-(i-1)) * new; fi;
                  if j > i+1 then new := Getbj(-(j-i-1)) * new; fi;
                  new := std.s[k] * new;
                  if j > i+1 then new := Getbj(j-i-1) * new; fi;
                  if i > 1 then new := Getai(i-1) * new; fi;
              elif i > j then
                  # We need to multiply from the left with the element
                  #    a^(j-1) * b^(i-j-1) * t_k * b^-(i-j-1) * a^-(j-1)
                  # from the left.
                  if j > 1 then new := Getai(-(j-1)) * new; fi;
                  if i > j+1 then new := Getbj(-(i-j-1)) * new; fi;
                  new := std.t[k] * new;
                  if i > j+1 then new := Getbj(i-j-1) * new; fi;
                  if j > 1 then new := Getai(j-1) * new; fi;
              fi;
              if not IsBound(std.cache[3][k][i]) then
                  std.cache[3][k][i] := [];
              fi;
              std.cache[3][k][i][j] := new;
          fi;
          std.left := new^coeffs[k] * std.left;
          newnew := new^coeffs[k] * newnew;
      fi;
  od;
  if m <> false and not IsZero(lambda) then m[i] := m[i] + m[j] * lambda; fi;
  return newnew;
end;

RECOG.DoColOp_SL := function(m,i,j,lambda,std)
  # add lambda times i-th column to j-th column, i<>j
  # by left-multiplying with an expression in the standard generators:
  #   a : e_n -> e_{n-1} -> ... -> e_1 -> (-1)^(n+1) e_n
  #   b : e_n -> e_{n-1} -> ... -> e_2 -> (-1)^n e_n and e_1 -> e_1
  #   s : e_1 -> e_1+ * e_2, e_i -> e_i   for i > 1
  #   t : e_2 -> e_1+ * e_2, e_i -> e_i   for i <> 2
  # s and t are lists of length ext to span over GF(p) all the scalars
  # in *.
  # Note that V_i = <e_1,...,e_i>.
  # So <s,t> is an SL_2 in the upper left corner, a is an n-cycle
  # b is an n-1 cycle with garbage fixing the first vector
  # This only modifies the record std collecting a straight line program.
  local Getai,Getbj,coeffs,k,new,newnew;

  Getai := function(l)
      local pos;
      if l < 0 then pos := std.d - l;
               else pos := l;
      fi;
      if not IsBound(std.cache[1][pos]) then
          std.cache[1][pos] := std.a^l;
      fi;
      return std.cache[1][pos];
  end;
  Getbj := function(l)
      local pos;
      if l < 0 then pos := std.d - l;
               else pos := l;
      fi;
      if not IsBound(std.cache[2][pos]) then
          std.cache[2][pos] := std.b^l;
      fi;
      return std.cache[2][pos];
  end;

  newnew := std.One;
  coeffs := RECOG.FindFFCoeffs(std,lambda);
  for k in [1..std.ext] do
      if not IsZero(coeffs[k]) then
          if IsBound(std.cache[4][k][i]) and
             IsBound(std.cache[4][k][i][j]) then
              new := std.cache[4][k][i][j];
          else;
              new := std.One;
              if i < j then
                  # We need to multiply from the right with the element
                  #    a^(i-1) * b^(j-i-1) * s_k * b^-(j-i-1) * a^-(i-1)
                  # from the right.
                  if i > 1 then new := Getai(-(i-1)) * new; fi;
                  if j > i+1 then new := Getbj(-(j-i-1)) * new; fi;
                  new := std.s[k] * new;
                  if j > i+1 then new := Getbj(j-i-1) * new; fi;
                  if i > 1 then new := Getai(i-1) * new; fi;
              elif i > j then
                  # We need to multiply from the right with the element
                  #    a^(j-1) * b^(i-j-1) * t_k * b^-(i-j-1) * a^-(j-1)
                  # from the left.
                  if j > 1 then new := Getai(-(j-1)) * new; fi;
                  if i > j+1 then new := Getbj(-(i-j-1)) * new; fi;
                  new := std.t[k] * new;
                  if i > j+1 then new := Getbj(i-j-1) * new; fi;
                  if j > 1 then new := Getai(j-1) * new; fi;
              fi;
              if not IsBound(std.cache[4][k][i]) then
                  std.cache[4][k][i] := [];
              fi;
              std.cache[4][k][i][j] := new;
          fi;
          std.right := std.right * new^coeffs[k];
          newnew := newnew * new^coeffs[k];
      fi;
  od;
  if m <> false and not IsZero(lambda) then
      for k in [1..Length(m)] do
          m[k][j] := m[k][j] + m[k][i] * lambda;
      od;
  fi;

  return newnew;
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
      x[1,2] := Z(p,ext)^i;
      Add(s,x);
      x := IdentityMat(d,f);
      x[2,1] := Z(p,ext)^i;
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
  if not IsOne(mi[1,1]) then
      if IsZero(mi[2,1]) then
          RECOG.DoRowOp_SL(mi,2,1,std.one,std);
          # Now mi[2,1] is non-zero
      fi;
      RECOG.DoRowOp_SL(mi,1,2,(std.one-mi[1,1])/mi[2,1],std);
  fi;
  # Now mi[1,1] is equal to one
  if not IsZero(mi[2,1]) then
      RECOG.DoRowOp_SL(mi,2,1,-mi[2,1],std);
  fi;
  # Now mi[2,1] is equal to zero and thus mi[2,2] equal to one
  if not IsZero(mi[1,2]) then
      RECOG.DoRowOp_SL(mi,1,2,-mi[1,2],std);
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
      if not IsOne(mi[i,i]) then
          pos := First([i+1..d],k->not IsZero(mi[k,i]));
          if pos = fail then
              pos := i+1;
              RECOG.DoRowOp_SL(mi,pos,i,std.one,std);
          fi;
          RECOG.DoRowOp_SL(mi,i,pos,(std.one-mi[i,i])/mi[pos,i],std);
      fi;
      # Now mi[i,i] is equal to one
      for j in Concatenation([1..i-1],[i+1..d]) do
          if not IsZero(mi[j,i]) then
              RECOG.DoRowOp_SL(mi,j,i,-mi[j,i],std);
          fi;
      od;
      # Now mi[i,i] is the only non-zero entry in the column
  od;
  # Now mi is the identity matrix, the element collected in std
  # is the one to multiply on the left hand side to transform mi to the
  # identity. Thus it is equal to m.
  return SLPOfElm(std.left);
end;



# TODO: which algorithm is this? reference?
RECOG.FindStdGens_SL := function(sld,f)
  # gens of sld must be gens for SL(d,q) in its natural rep with memory
  # This function calls RECOG.SLn_constructsl2 and then extends
  # the basis to a basis of the full row space and calls
  # RECOG.SLn_UpStep often enough. Finally it returns an slp such
  # that the SL(d,q) standard generators with respect to this basis are
  # expressed by the slp in terms of the original generators of sld.
  local V,b,bas,basi,basit,d,data,ext,fakegens,id,nu,nu2,p,q,resl2,sl2,sl2gens,
        sl2gensf,sl2genss,sl2stdf,slp,slpsl2std,slptosl2,st,std,stdgens,i,ex;

  # Some setup:
  p := Characteristic(f);
  q := Size(f);
  ext := DegreeOverPrimeField(f);
  d := DimensionOfMatrixGroup(sld);
  if not IsObjWithMemory(GeneratorsOfGroup(sld)[1]) then
      sld := GroupWithMemory(sld);
  fi;

  # First find an SL2 with the space it acts on:
  Info(InfoRecog,2,"Finding an SL2...");
  data := RECOG.SLn_constructsl2(sld,d,q);

  bas := ShallowCopy(BasisVectors(Basis(data[2])));
  sl2 := data[1];
  slptosl2 := SLPOfElms(GeneratorsOfGroup(sl2));
  sl2gens := StripMemory(GeneratorsOfGroup(sl2));
  V := data[2];
  b := Basis(V,bas);
  sl2genss := List(sl2gens,x->RECOG.LinearAction(b,f,x));

  if q in [2,3,4,5,9] then
      Info(InfoRecog,2,"In fact found an SL4...");
      stdgens := RECOG.MakeSL_StdGens(p,ext,4,4).all;
      slpsl2std := RECOG.FindStdGensUsingBSGS(Group(sl2genss),stdgens,
                                              false,false);
      nu := List(sl2gens,x->NullspaceMat(x-One(x)));
      ex := SumIntersectionMat(nu[1],nu[2])[2];
      for i in [3..Length(nu)] do
          ex := SumIntersectionMat(nu[3],ex);
      od;
      Append(bas,ex);
      ConvertToMatrixRep(bas,q);
      basi := bas^-1;
  else
      # Now compute the natural SL2 action and run constructive recognition:
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
      st := ResultOfStraightLineProgram(slp,
                                        StripMemory(GeneratorsOfGroup(sl2)));

      # Extend basis by something invariant under SL2:
      id := IdentityMat(d,f);
      nu := NullspaceMat(StripMemory(st[1]-id));
      nu2 := NullspaceMat(StripMemory(st[2]-id));
      Append(bas,SumIntersectionMat(nu,nu2)[2]);
      ConvertToMatrixRep(bas,q);
      basi := bas^-1;
  fi;

  # Now set up fake generators for keeping track what we do:
  fakegens := ListWithIdenticalEntries(Length(GeneratorsOfGroup(sld)),1);
  fakegens := GeneratorsWithMemory(fakegens);
  sl2gensf := ResultOfStraightLineProgram(slptosl2,fakegens);
  sl2stdf := ResultOfStraightLineProgram(slpsl2std,sl2gensf);
  std := rec( f := f, d := d, n := 2, bas := bas, basi := basi,
              sld := sld, sldf := fakegens, slnstdf := sl2stdf,
              p := p, ext := ext );
  Info(InfoRecog,2,"Going up to SL_d again...");
  while std.n < std.d do
      RECOG.SLn_UpStep(std);
  od;
  return rec( slpstd := SLPOfElms(std.slnstdf),
              bas := std.bas, basi := std.basi );
end;

RECOG.RecogniseSL2NaturalOddCharUsingBSGS := function(g,f)
  local ext,p,q,res,slp,std;
  p := Characteristic(f);
  ext := DegreeOverPrimeField(f);
  q := Size(f);
  std := RECOG.MakeSL_StdGens(p,ext,2,2);
  slp := RECOG.FindStdGensUsingBSGS(g,std.all,false,true);
  if slp = fail then
      return fail;
  fi;
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
  # f a finite field, g equal to SL(2,Size(f)), t either an involution
  # or false.
  # Returns a set of standard generators for SL_2 and the base change
  # to expose it. Works with memory. Uses PseudoRandom.
  local a,actpos,am,b,bas,bm,c,can,ch,cm,co,co2,el,ev,eva,evb,evbi,ext,gens,
        i,j,k,kk,mas,masi,mat,mati,mb,o,one,os,pos,q,res,s,ss,ssm,t,tb,tm,
        tt,ttm,u,v,x,xb,xm;

  q := Size(f);
  gens := GeneratorsOfGroup(g);
  if torig = false then
      for a in gens do
          if not IsOne(a) and IsOne(a^2) then
              torig := a;
              break;
          fi;
      od;
  fi;
  if torig = false then
    # if no involution t has been given, compute one, using Proposition 4 from
    # [KK15].
    repeat
        am:=PseudoRandom(g);
    until not IsOneProjective(am);
    k := Order(am);
    if IsEvenInt(k) then
        tm := am^(k/2);
    else
        # find a conjugate of a which does not commute with a.
        repeat
            bm := am^PseudoRandom(g);
            cm := am*bm;
            tm := bm*am;
        until cm<>tm;
        tm := tm^-1 * cm;
        if not IsOneProjective(StripMemory(tm)^2) then
            tm := cm^((q^2-2)/2) * am;
        fi;
    fi;
  else
      tm := torig;
  fi;
  t := StripMemory(tm);

  Assert(1, IsOne(t^2));

  ch := Factors(CharacteristicPolynomial(f,f,t,1));
  if Length(ch) <> 2 or ch[1] <> ch[2] then
      ErrorNoReturn("matrix is not triagonalizable - this should never happen!");
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
  mat := [Coefficients(can,tb[2,1])];
  mb := MutableBasis(GF(2),mat);
  o := [gens[1]];
  os := [gens[1]];
  actpos := 1;
  j := 1;
  ext := DegreeOverPrimeField(f);
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
          until not IsOne(c^2);
          xm := xm * c^(((q-1)*(q+1)-1)/2);
          x := StripMemory(xm);
          xb := bas*x*bas^-1;
          co := Coefficients(can,xb[2,1]);
      until not IsContainedInSpan(mb,co);
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
          until not IsZero(x[1,2]);

          if not IsOne(x[2,2]) then
              el := (One(f)-x[2,2])/x[1,2];
              co := Coefficients(can,el) * mati;
              for i in [1..Length(co)] do
                  if not IsZero(co[i]) then
                      xm := ttm[i] * xm;
                  fi;
              od;
              x[2] := x[2] + x[1] * el;
              if x <> bas*StripMemory(xm)*bas^-1 then
                # FIXME: sometimes triggered by RecognizeGroup(GL(2,16));
                ErrorNoReturn("!!!");
              fi;
          fi;
          # now x[2,2] is equal to One(f)
          # we postpone the actual computation of the final x until we
          # know it is needed:
          co := Coefficients(can,x[1,2]);
          if IsContainedInSpan(mb,co) then continue; fi;
          # OK, we need it, so let's make it:
          el := x[2,1];
          co2 := Coefficients(can,el) * mati;
          for i in [1..Length(co2)] do
              if not IsZero(co2[i]) then
                  xm := xm * ttm[i];
              fi;
          od;
# TODO: add sanity check here, too???
          x := StripMemory(xm);
          # now x[2,1] is equal to Zero(f) and thus x[1,1] is One(f) as well
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
              One := One(s[1]), f := f, q := q, p := 2, ext := ext,
              d := 2 );
  res.all := Concatenation(res.s,res.t,[res.a],[res.b]);
  return res;
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
      if IsOneProjective(y) then
          return p;
      fi;
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
          if not IsOneProjective(z) then break; fi;
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

  # The following method does not work for q <= 11, as then
  # the projective orders are either q+1, or else less than 5.
  # Hence seenqm1 never gets set.
  CheckElm := function(x)
      local o;
      o := RECOG.GuessProjSL2ElmOrder(x,f);
      if o in [1,2] then
          return false;
      fi;
      if o > 5 then
          if notA5 = false then Info(InfoRecog,4,"SL2: Group is not A5"); fi;
          notA5 := true;
          if seenqp1 and seenqm1 then
              return true;
          fi;
      fi;
      if o = p or o <= 5 then
          return false;
      fi;
      if (q+1) mod o = 0 then
          if not seenqp1 then
              Info(InfoRecog,4,"SL2: Found element of order dividing q+1.");
              seenqp1 := true;
              if seenqm1 and notA5 then
                  return true;
              fi;
          fi;
      else
          if not seenqm1 then
              Info(InfoRecog,4,"SL2: Found element of order dividing q-1.");
              seenqm1 := true;
              if seenqp1 and notA5 then
                  return true;
              fi;
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
  # For small q, compute the order of the group via a stabilizer chain.
  # Note that at this point we are usually working projective, and thus
  # scalars are factored out "implicitly". Thus the generators we are
  # looking at may generate a group which only contains SL2 as a subgroup.
  if q <= 11 then    # this could be increased if needed
      Info(InfoRecog,4,"SL2: Computing stabiliser chain.");
      S := StabilizerChain(Group(gens));
      Info(InfoRecog,4,"SL2: size is ",Size(S));
      return Size(S) mod (q*(q-1)*(q+1)) = 0;
  fi;

  seenqp1 := false;
  seenqm1 := false;
  notA5 := false;

  for i in [1..Length(gens)] do
      if CheckElm(gens[i]) then
          return true;
      fi;
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
              if CheckElm(x) then
                  return true;
              fi;
              Add(coms,x);
          od;
      od;
  else
      Info(InfoRecog,4,"SL2: Computing 6 random commutators...");
      for i in [1..6] do
          a := RECOG.RandomSubproduct(gens,rec());
          b := RECOG.RandomSubproduct(gens,rec());
          x := Comm(a,b);
          if CheckElm(x) then
              return true;
          fi;
          Add(coms,x);
      od;
  fi;
  if ForAll(coms, RECOG.IsScalarMat) then
      Info(InfoRecog,4,"SL2: Group is soluble, commutators are central");
      return false;
  fi;
  Info(InfoRecog,4,"SL2: Computing normal closure...");
  clos := FastNormalClosure(gens,coms,5);
  for i in [Length(coms)+1..Length(clos)] do
      if CheckElm(clos[i]) then
          return true;
      fi;
  od;
  if ForAll(clos{[Length(coms)+1..Length(clos)]}, RECOG.IsScalarMat) then
      Info(InfoRecog,4,"SL2: Group is soluble, derived subgroup central");
      return false;
  fi;
  Info(InfoRecog,4,"SL2: Computing 6 random commutators...");
  isabelian := true;
  for i in [1..6] do
      a := RECOG.RandomSubproduct(clos,rec());
      b := RECOG.RandomSubproduct(clos,rec());
      x := Comm(a,b);
      if not RECOG.IsScalarMat(x) then isabelian := false; break; fi;
  od;
  if isabelian then
      Info(InfoRecog,4,
           "SL2: Group is soluble, derived subgroup abelian mod scalars");
      return false;
  fi;

  # Now we know that the group is not dihedral!
  return false;
end;

# The going down method:

#Version 1.2

# finds first element of a list that is relative prime to all others
# input: list=[SL(d,q), d, q, SL(n,q)] acting as a subgroup of some big SL(n,q)
# output: list=[rr, dd] for a ppd(2*dd;q)-element rr
RECOG.SLn_godown:=function(list)
  local d, first, q, g, gg, i, r, pol, factors, degrees, newdim, power, rr, ss,
  newgroup, colldegrees, exp, count;

  first:=function(list)
  local i;

  for i in [1..Length(list)] do
      if list[i]>1 and Gcd(list[i],Product(list)/list[i])=1 then
         return list[i];
      fi;
  od;

  return fail;
  end;

  g:=list[1];
  d:=list[2];
  q:=list[3];
  gg:=list[4];

  Info(InfoRecog,2,"Dimension: ",d);
  #find an element with irreducible action of relative prime dimension to
  #all other invariant subspaces
  #count is just safety, if things go very bad
  count:=0;

  repeat
     count:=count+1;
  if InfoLevel(InfoRecog) >= 3 then Print(".\c"); fi;
     r:=PseudoRandom(g);
     pol:=CharacteristicPolynomial(r);
     factors:=Factors(pol);
     degrees:=AsSortedList(List(factors,Degree));
     newdim:=first(degrees);
  until (count>10) or (newdim <> fail and newdim<=Maximum(2,d/4));

  if count>10 then
     return fail;
  fi;

  # raise r to a power so that acting trivially outside one invariant subspace
  degrees:=Filtered(degrees, x->x<>newdim);
  colldegrees:=Collected(degrees);
  power:=Lcm(List(degrees, x->q^x-1))*q;
  # power further to cancel q-part of element order
  if degrees[1]=1 then
     exp:=colldegrees[1][2]-(DimensionOfMatrixGroup(gg)-d);
     if exp>0 then
       power:=power*q^exp;
     fi;
  fi;
  rr:=r^power;

  #conjugate rr to hopefully get a smaller dimensional SL
  #ss:=rr^PseudoRandom(gg);
  #newgroup:=Group(rr,ss);

  return [rr,newdim];
end;

# input is (group,dimension,q)
# output is a group element acting irreducibly in two dimensions, and fixing
# a (dimension-2)-dimensional subspace
RECOG.SLn_constructppd2:=function(g,dim,q)
  local out, list ;

  list:=[g,dim,q,g];
  repeat
     out:=RECOG.SLn_godown(list);
     if out=fail or out[1]*out[1]=One(out[1]) then
        if InfoLevel(InfoRecog) >= 3 then Print("B\c"); fi;
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

RECOG.SLn_constructsl4:=function(g,dim,q,r)
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


#g=SL(d,q), given as a subgroup of SL(dim,q)
#output: [SL(2,q), and a basis for the 2-dimensional subspace where it acts
RECOG.SLn_godownfromd:=function(g,q,d,dim)
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
               (1 in Set(dims)) then
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
     if InfoLevel(InfoRecog) >= 3 then Print("C"); fi;
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

  r:=RECOG.SLn_constructppd2(g,d,q);
  h:=RECOG.SLn_constructsl4(g,d,q,r);
  if not (q in [2,3,4,5,9]) then
     return RECOG.SLn_godownfromd(h,q,4,d);
  else
     return RECOG.SLn_exceptionalgodown(h,q,d);
  #   return ["sorry only SL(4,q)",h];
  fi;
end;

# Now the going up code:

RECOG.LinearAction := function(bas,field,el)
  local mat,vecs;
  if IsGroup(el) then
      return Group(List(GeneratorsOfGroup(el),
                        x->RECOG.LinearAction(bas,field,x)));
  fi;
  if IsBasis(bas) then
      vecs := BasisVectors(bas);
  else
      vecs := bas;
      bas := Basis(VectorSpace(field,bas),bas);
  fi;
  mat := List(vecs,v->Coefficients(bas,v*el));
  ConvertToMatrixRep(mat,field);
  return mat;
end;

RECOG.SLn_UpStep := function(w)
  # w has components:
  #   d       : size of big SL
  #   n       : size of small SL
  #   slnstdf : fakegens for SL_n standard generators
  #   bas     : current base change, first n vectors are where SL_n acts
  #             rest of vecs are invariant under SL_n
  #   basi    : current inverse of bas
  #   sld     : original group with memory generators, PseudoRandom
  #             delivers random elements
  #   sldf    : fake generators to keep track of what we are doing
  #   f       : field
  # The following are filled in automatically if not already there:
  #   p       : characteristic
  #   ext     : q=p^ext
  #   One     : One(slnstdf[1])
  #   can     : CanonicalBasis(f)
  #   canb    : BasisVectors(can)
  #   transh  : fakegens for the "horizontal" transvections n,i for 1<=i<=n-1
  #             entries can be unbound in which case they are made from slnstdf
  #   transv  : fakegens for the "vertical" transvections i,n for 1<=i<=n-1
  #             entries can be unbound in which case they are made from slnstdf
  #
  # We keep the following invariants (going from n -> n':=2n-1)
  #   bas, basi is a base change to the target base
  #   slnstdf are SLPs to reach standard generators of SL_n from the
  #       generators of sld
  local DoColOp_n,DoRowOp_n,FixSLn,Fixc,MB,Vn,Vnc,aimdim,c,c1,c1f,cf,cfi,
        ci,cii,coeffs,flag,i,id,int1,int3,j,k,lambda,list,mat,newbas,newbasf,
        newbasfi,newbasi,newdim,newpart,perm,pivots,pivots2,pos,pow,s,sf,
        slp,std,sum1,tf,trans,transd,transr,v,vals,zerovec;

  Info(InfoRecog,3,"Going up: ",w.n," (",w.d,")...");

  # Before we begin, we upgrade the data structure with a few internal
  # things:

  if not IsBound(w.can) then w.can := CanonicalBasis(w.f); fi;
  if not IsBound(w.canb) then w.canb := BasisVectors(w.can); fi;
  if not IsBound(w.One) then w.One := One(w.slnstdf[1]); fi;
  if not IsBound(w.transh) then w.transh := []; fi;
  if not IsBound(w.transv) then w.transv := []; fi;
  # Update our cache of *,n and n,* transvections because we need them
  # all over the place:
  std := RECOG.InitSLstd(w.f,w.n,
                         w.slnstdf{[1..w.ext]},
                         w.slnstdf{[w.ext+1..2*w.ext]},
                         w.slnstdf[2*w.ext+1],
                         w.slnstdf[2*w.ext+2]);
  for i in [1..w.n-1] do
      for k in [1..w.ext] do
          pos := (i-1)*w.ext + k;
          if not IsBound(w.transh[pos]) then
              RECOG.ResetSLstd(std);
              RECOG.DoColOp_SL(false,w.n,i,w.canb[k],std);
              w.transh[pos] := std.right;
          fi;
          if not IsBound(w.transv[pos]) then
              RECOG.ResetSLstd(std);
              RECOG.DoRowOp_SL(false,i,w.n,w.canb[k],std);
              w.transv[pos] := std.left;
          fi;
      od;
  od;
  Unbind(std);

  # Now we can define two helper functions:
  DoColOp_n := function(el,i,j,lambda,w)
    # This adds lambda times the i-th column to the j-th column.
    # Note that either i or j must be equal to n!
    local coeffs,k;
    coeffs := IntVecFFE(Coefficients(w.can,lambda));
    if i = w.n then
        for k in [1..w.ext] do
            if not IsZero(coeffs[k]) then
                if IsOne(coeffs[k]) then
                    el := el * w.transh[(j-1)*w.ext+k];
                else
                    el := el * w.transh[(j-1)*w.ext+k]^coeffs[k];
                fi;
            fi;
        od;
    elif j = w.n then
        for k in [1..w.ext] do
            if not IsZero(coeffs[k]) then
                if IsOne(coeffs[k]) then
                    el := el * w.transv[(i-1)*w.ext+k];
                else
                    el := el * w.transv[(i-1)*w.ext+k]^coeffs[k];
                fi;
            fi;
        od;
    else
        ErrorNoReturn("either i or j must be equal to n");
    fi;
    return el;
  end;
  DoRowOp_n := function(el,i,j,lambda,w)
    # This adds lambda times the j-th row to the i-th row.
    # Note that either i or j must be equal to n!
    local coeffs,k;
    coeffs := IntVecFFE(Coefficients(w.can,lambda));
    if j = w.n then
        for k in [1..w.ext] do
            if not IsZero(coeffs[k]) then
                if IsOne(coeffs[k]) then
                    el := w.transv[(i-1)*w.ext+k] * el;
                else
                    el := w.transv[(i-1)*w.ext+k]^coeffs[k] * el;
                fi;
            fi;
        od;
    elif i = w.n then
        for k in [1..w.ext] do
            if not IsZero(coeffs[k]) then
                if IsOne(coeffs[k]) then
                    el := w.transh[(j-1)*w.ext+k] * el;
                else
                    el := w.transh[(j-1)*w.ext+k]^coeffs[k] * el;
                fi;
            fi;
        od;
    else
        ErrorNoReturn("either i or j must be equal to n");
    fi;
    return el;
  end;

  # Here everything starts, some more preparations:

  # We compute exclusively in our basis, so we occasionally need an
  # identity matrix:
  id := IdentityMat(w.d,w.f);
  FixSLn := VectorSpace(w.f,id{[w.n+1..w.d]});
  Vn := VectorSpace(w.f,id{[1..w.n]});

  # First pick an element in SL_n with fixed space of dimension d-n+1:
  # We already have an SLP for an n-1-cycle: it is one of the std gens.
  # For n=2 we use a transvection for this purpose.
  if w.n > 2 then
      if IsOddInt(w.n) then
          if w.p > 2 then
            s := id{Concatenation([1,w.n],[2..w.n-1],[w.n+1..w.d])};
            ConvertToMatrixRepNC(s,w.f);
            if IsOddInt(w.n) then s[2] := -s[2]; fi;
            sf := w.slnstdf[2*w.ext+2];
          else   # in even characteristic we take the n-cycle:
            s := id{Concatenation([w.n],[1..w.n-1],[w.n+1..w.d])};
            ConvertToMatrixRepNC(s,w.f);
            sf := w.slnstdf[2*w.ext+1];
          fi;
      else
          ErrorNoReturn("this program only works for odd n or n=2");
      fi;
  else
      # In this case the n-1-cycle is the identity, so we take a transvection:
      s := MutableCopyMat(id);
      s[1,2] := One(w.f);
      sf := w.slnstdf[1];
  fi;

  # Find a good random element:
  w.count := 0;
  aimdim := Minimum(2*w.n-1,w.d);
  newdim := aimdim - w.n;
  while true do   # will be left by break
      while true do    # will be left by break
          if InfoLevel(InfoRecog) >= 3 then Print(".\c"); fi;
          w.count := w.count + 1;
          c1 := PseudoRandom(w.sld);
          slp := SLPOfElm(c1);
          c1f := ResultOfStraightLineProgram(slp,w.sldf);
          # Do the base change into our basis:
          c1 := w.bas * c1 * w.basi;
          c := s^c1;
          cf := sf^c1f;
          cfi := cf^-1;
          # Now check that Vn + Vn*s^c1 has dimension 2n-1:
          Vnc := VectorSpace(w.f,c{[1..w.n]});
          sum1 := ClosureLeftModule(Vn,Vnc);
          if Dimension(sum1) = aimdim then
              Fixc := VectorSpace(w.f,NullspaceMat(c-One(c)));
              int1 := Intersection(Fixc,Vn);
              for i in [1..Dimension(int1)] do
                  v := Basis(int1)[i];
                  if not IsZero(v[w.n]) then break; fi;
              od;
              if IsZero(v[w.n]) then
                  Info(InfoRecog,2,"Ooops: Component n was zero!");
                  continue;
              fi;
              v := v / v[w.n];   # normalize to 1 in position n
              Assert(1,v*c=v);
              ci := c^-1;
              break;
          fi;
      od;

      # Now we found our aimdim-dimensional space W. Since SL_n
      # has a d-n-dimensional fixed space W_{d-n} and W contains a complement
      # of that fixed space, the intersection of W and W_{d-n} has dimension
      # newdim.

      # Change basis:
      newpart := ExtractSubMatrix(c,[1..w.n-1],[1..w.d]);
      # Clean out the first n entries to go to the fixed space of SL_n:
      zerovec := Zero(newpart[1]);
      for i in [1..w.n-1] do
          CopySubVector(zerovec,newpart[i],[1..w.n],[1..w.n]);
      od;
      MB := MutableBasis(w.f,[],zerovec);
      i := 1;
      pivots := EmptyPlist(newdim);
      while i <= Length(newpart) and NrBasisVectors(MB) < newdim do
          if not IsContainedInSpan(MB,newpart[i]) then
              Add(pivots,i);
              CloseMutableBasis(MB,newpart[i]);
          fi;
          i := i + 1;
      od;
      newpart := newpart{pivots};
      newbas := Concatenation(id{[1..w.n-1]},[v],newpart);
      if 2*w.n-1 < w.d then
          int3 := Intersection(FixSLn,Fixc);
          if Dimension(int3) <> w.d-2*w.n+1 then
              Info(InfoRecog,2,"Ooops, FixSLn \cap Fixc wrong dimension");
              continue;
          fi;
          Append(newbas,BasisVectors(Basis(int3)));
      fi;
      ConvertToMatrixRep(newbas,w.f);
      newbasi := newbas^-1;
      if newbasi = fail then
          Info(InfoRecog,2,"Ooops, Fixc intersected too much, we try again");
          continue;
      fi;
      ci := newbas * ci * newbasi;
      cii := ExtractSubMatrix(ci,[w.n+1..aimdim],[1..w.n-1]);
      ConvertToMatrixRep(cii,w.f);
      cii := TransposedMat(cii);
      # The rows of cii are now what used to be the columns,
      # their length is newdim, we need to span the full newdim-dimensional
      # row space and need to remember how:
      zerovec := Zero(cii[1]);
      MB := MutableBasis(w.f,[],zerovec);
      i := 1;
      pivots2 := EmptyPlist(newdim);
      while i <= Length(cii) and NrBasisVectors(MB) < newdim do
          if not IsContainedInSpan(MB,cii[i]) then
              Add(pivots2,i);
              CloseMutableBasis(MB,cii[i]);
          fi;
          i := i + 1;
      od;
      if Length(pivots2) = newdim then
          cii := cii{pivots2}^-1;
          ConvertToMatrixRep(cii,w.f);
          c := newbas * c * newbasi;
          w.bas := newbas * w.bas;
          w.basi := w.basi * newbasi;
          break;
      fi;
      Info(InfoRecog,2,"Ooops, no nice bottom...");
      # Otherwise simply try again
  od;
  Info(InfoRecog,2," found c1 and c.");
  # Now SL_n has to be repaired according to the base change newbas:

  # Now write this matrix newbas as an SLP in the standard generators
  # of our SL_n. Then we know which generators to take for our new
  # standard generators, namely newbas^-1 * std * newbas.
  newbasf := w.One;
  for i in [1..w.n-1] do
      if not IsZero(v[i]) then
          newbasf := DoColOp_n(newbasf,w.n,i,v[i],w);
      fi;
  od;
  newbasfi := newbasf^-1;
  w.slnstdf := List(w.slnstdf,x->newbasfi * x * newbasf);
  # Now update caches:
  w.transh := List(w.transh,x->newbasfi * x * newbasf);
  w.transv := List(w.transv,x->newbasfi * x * newbasf);

  # Now consider the transvections t_i:
  # t_i : w.bas[j] -> w.bas[j]        for j <> i and
  # t_i : w.bas[i] -> w.bas[i] + ww
  # We want to modify (t_i)^c such that it fixes w.bas{[1..w.n]}:
  trans := [];
  for i in pivots2 do
      # This does t_i
      for lambda in w.canb do
          # This does t_i : v_j -> v_j + lambda * v_n
          tf := w.One;
          tf := DoRowOp_n(tf,i,w.n,lambda,w);
          # Now conjugate with c:
          tf := cfi*tf*cf;
          # Now cleanup in column n above row n, the entries there
          # are lambda times the stuff in column i of ci:
          for j in [1..w.n-1] do
              tf := DoRowOp_n(tf,j,w.n,-ci[j,i]*lambda,w);
          od;
          Add(trans,tf);
      od;
  od;

  # Now put together the clean ones by our knowledge of c^-1:
  transd := [];
  for i in [1..Length(pivots2)] do
      for lambda in w.canb do
          tf := w.One;
          vals := BlownUpVector(w.can,cii[i]*lambda);
          for j in [1..w.ext * newdim] do
              pow := IntFFE(vals[j]);
              if not IsZero(pow) then
                  if IsOne(pow) then
                      tf := tf * trans[j];
                  else
                      tf := tf * trans[j]^pow;
                  fi;
              fi;
          od;
          Add(transd,tf);
      od;
  od;
  Unbind(trans);

  # Now to the "horizontal" transvections, first create them as SLPs:
  transr := [];
  for i in pivots do
      # This does u_i : v_i -> v_i + v_n
      tf := w.One;
      tf := DoColOp_n(tf,w.n,i,One(w.f),w);
      # Now conjugate with c:
      tf := cfi*tf*cf;
      # Now cleanup in rows above row n:
      for j in [1..w.n-1] do
          tf := DoRowOp_n(tf,j,w.n,-ci[j,w.n],w);
      od;
      # Now cleanup in rows below row n:
      for j in [1..newdim] do
          coeffs := IntVecFFE(Coefficients(w.can,-ci[w.n+j,w.n]));
          for k in [1..w.ext] do
              if not IsZero(coeffs[k]) then
                  if IsOne(coeffs[k]) then
                      tf := transd[(j-1)*w.ext + k] * tf;
                  else
                      tf := transd[(j-1)*w.ext + k]^coeffs[k] * tf;
                  fi;
              fi;
          od;
      od;
      # Now cleanup column n above row n:
      for j in [1..w.n-1] do
          tf := DoColOp_n(tf,j,w.n,ci[j,w.n],w);
      od;
      # Now cleanup row n left of column n:
      for j in [1..w.n-1] do
          tf := DoRowOp_n(tf,w.n,j,-c[i,j],w);
      od;
      # Now cleanup column n below row n:
      for j in [1..newdim] do
          coeffs := IntVecFFE(Coefficients(w.can,ci[w.n+j,w.n]));
          for k in [1..w.ext] do
              if not IsZero(coeffs[k]) then
                  if IsOne(coeffs[k]) then
                      tf := tf * transd[(j-1)*w.ext + k];
                  else
                      tf := tf * transd[(j-1)*w.ext + k]^coeffs[k];
                  fi;
              fi;
          od;
      od;
      Add(transr,tf);
  od;

  # From here on we distinguish three cases:
  #   * w.n = 2
  #   * we finish off the constructive recognition
  #   * we have to do another step as the next thing
  if w.n = 2 then
      w.slnstdf[2*w.ext+2] := transd[1]*transr[1]^-1*transd[1];
      w.slnstdf[2*w.ext+1] := w.transh[1]*w.transv[1]^-1*w.transh[1]
                              *w.slnstdf[2*w.ext+2];
      Unbind(w.transh);
      Unbind(w.transv);
      w.n := 3;
      return w;
  fi;
  # We can finish off:
  if aimdim = w.d then
      # In this case we just finish off and do not bother with
      # the transvections, we will only need the standard gens:
      # Now put together the (newdim+1)-cycle:
      # n+newdim -> n+newdim-1 -> ... -> n+1 -> n -> n+newdim
      flag := false;
      s := w.One;
      for i in [1..newdim] do
          if flag then
              # Make [[0,-1],[1,0]] in coordinates w.n and w.n+i:
              tf:=transd[(i-1)*w.ext+1]*transr[i]^-1*transd[(i-1)*w.ext+1];
          else
              # Make [[0,1],[-1,0]] in coordinates w.n and w.n+i:
              tf:=transd[(i-1)*w.ext+1]^-1*transr[i]*transd[(i-1)*w.ext+1]^-1;
          fi;
          s := s * tf;
          flag := not flag;
      od;

      # Finally put together the new 2n-1-cycle and 2n-2-cycle:
      s := s^-1;
      w.slnstdf[2*w.ext+1] := w.slnstdf[2*w.ext+1] * s;
      w.slnstdf[2*w.ext+2] := w.slnstdf[2*w.ext+2] * s;
      Unbind(w.transv);
      Unbind(w.transh);
      w.n := aimdim;
      return w;
  fi;

  # Otherwise we do want to go on as the next thing, so we want to
  # keep our transvections. This is easily done if we change the
  # basis one more time. Note that we know that n is odd here!

  # Put together the n-cycle:
  # 2n-1 -> 2n-2 -> ... -> n+1 -> n -> 2n-1
  flag := false;
  s := w.One;
  for i in [w.n-1,w.n-2..1] do
      if flag then
          # Make [[0,-1],[1,0]] in coordinates w.n and w.n+i:
          tf := transd[(i-1)*w.ext+1]*transr[i]^-1*transd[(i-1)*w.ext+1];
      else
          # Make [[0,1],[-1,0]] in coordinates w.n and w.n+i:
          tf := transd[(i-1)*w.ext+1]^-1*transr[i]*transd[(i-1)*w.ext+1]^-1;
      fi;
      s := s * tf;
      flag := not flag;
  od;

  # Finally put together the new 2n-1-cycle and 2n-2-cycle:
  w.slnstdf[2*w.ext+1] := s * w.slnstdf[2*w.ext+1];
  w.slnstdf[2*w.ext+2] := s * w.slnstdf[2*w.ext+2];

  list := Concatenation([1..w.n-1],[w.n+1..2*w.n-1],[w.n],[2*w.n..w.d]);
  perm := PermList(list);
  mat := PermutationMat(perm^-1,w.d,w.f);
  ConvertToMatrixRep(mat,w.f);
  w.bas := w.bas{list};
  ConvertToMatrixRep(w.bas,w.f);
  w.basi := w.basi*mat;

  # Now add the new transvections:
  for i in [1..w.n-1] do
      w.transh[w.ext*(w.n-1)+w.ext*(i-1)+1] := transr[i];
  od;
  Append(w.transv,transd);
  w.n := 2*w.n-1;
  return w;
end;


# Now the code for writing SLPs:

SLPforElementFuncsProjective.PSL2 := function(ri,x)
  local det,log,slp,y,z,pos,s;
  ri!.fakegens.count := ri!.fakegens.count + 1;
  if ri!.fakegens.count > 1000 then
      ri!.fakegens := RECOG.InitSLfake(ri!.field,2);
      ri!.fakegens.count := 0;
  fi;
  y := ri!.nicebas * x * ri!.nicebasi;
  det := DeterminantMat(y);
  if not IsOne(det) then
      z := PrimitiveRoot(ri!.field);
      log := LogFFE(det,z);
      y := y * z^(-log*ri!.gcd.coeff1/ri!.gcd.gcd);
  fi;
  # At this point, y has determinant 1; but we consider it modulo scalars.
  # To make sure that different coset reps behave the same, we scale it
  # with a suitable primitive d-th root of unity.
  if not IsBound(ri!.normlist) then
      ri!.normlist := RECOG.SetupNormalisationListForPSLd(ri!.field,
                                                          ri!.gcd.gcd);
  fi;
  pos := PositionNonZero(y[1]);
  s := RECOG.NormaliseScalarForPSLd(y[1,pos],ri!.normlist);
  slp := RECOG.ExpressInStd_SL2(s * y,ri!.fakegens);
  return slp;
end;

# s: a non-zero scalar
# list: a list of certain primitive roots of unity, as
#       computed by SetupNormalisationListForPSLd
#
# This function considers s and all its multiples by the elements in
# list, and picks the smallest of them. It returns the multiplicator
# used to obtain that element from s.
RECOG.NormaliseScalarForPSLd := function(s,list)
  local min,minmul,t,u;
  min := s;
  minmul := s^0;
  for t in list do
      u := s*t;
      if u < min then
          min := u;
          minmul := t;
      fi;
  od;
  return minmul;
end;

# f: a finite field
# d: a positive integer
#
# Returns a list of primitive d-th roots of unity.
RECOG.SetupNormalisationListForPSLd := function(f,d)
  local e,i,list,z;
  list := EmptyPlist(d);
  z := PrimitiveRoot(f)^((Size(f)-1)/d);
  e := z;
  for i in [1..d-1] do
      Add(list,e);
      e := e * z;
  od;
  return list;
end;

# el: a field element
# d: a positive integer (typically ri!.gcd.gcd)
# f: a galois field (typically ri!.field)
#
# Compute a primitive d-th root of el in the field f.
# TODO: This function copies the code from RootFFE, which will
# appear in GAP 4.9. Once GAP 4.9 is out, we can switch
# to using RootFFE directly.
RECOG.ComputeRootInFiniteField := function(el, d, f)
    local z, e, m, p, a;
    if IsZero(el) or IsOne(el)  then
        return el;
    fi;
    z := PrimitiveRoot(f);
    m := Size(f) - 1;
    e := LogFFE(el, z);
    p := GcdInt(m, e);
    d := d mod m;
    a := GcdInt(m, d);
    if p mod a <> 0  then
        return fail;
    fi;
    a := e * (a / d mod (m / p)) / a mod m;
    return z ^ a;
end;

# Express an element of PSL_d as an slp in terms of standard generators.
SLPforElementFuncsProjective.PSLd := function(ri,x)
  local det,pos,root,s,slp,y;
  ri!.fakegens.count := ri!.fakegens.count + 1;
  if ri!.fakegens.count > 1000 then
      ri!.fakegens := RECOG.InitSLfake(ri!.field,ri!.dimension);
      ri!.fakegens.count := 0;
  fi;
  y := ri!.nicebas * x * ri!.nicebasi;
  det := DeterminantMat(y);
  if not IsOne(det) then
      # At this point, y is in the kernel of the determinant map *mod scalars*.
      # That means that det may not be 1 -- it can be any d-th power.
      # We thus can compute a d-th root of 1/det, and scale y with it,
      # in order to obtain a matrix with determinant 1 in the same
      # projective class.
      root := RECOG.ComputeRootInFiniteField(1/det,Length(y),ri!.field);
      if root = fail then
          return fail;
      fi;
      y := y * root;
  fi;
  # At this point, y has determinant 1; but we consider it modulo scalars.
  # To make sure that different coset reps behave the same, we scale it
  # with a suitable primitive d-th root of unity.
  if not IsBound(ri!.normlist) then
      ri!.normlist := RECOG.SetupNormalisationListForPSLd(ri!.field,
                                                          ri!.gcd.gcd);
  fi;
  pos := PositionNonZero(y[1]);
  s := RECOG.NormaliseScalarForPSLd(y[1,pos],ri!.normlist);
  slp := RECOG.ExpressInStd_SL(s * y,ri!.fakegens);
  return slp;
end;

#! @BeginChunk ClassicalNatural
#! TODO
#! @EndChunk
BindRecogMethod(FindHomMethodsProjective, "ClassicalNatural",
"check whether it is a classical group in its natural representation",
function(ri, g)
  local changed,classical,d,det,ext,f,gcd,gens,gm,i,p,pr,q,root,std,stdg,z;
  d := ri!.dimension;
  f := ri!.field;
  q := Size(f);
  p := Characteristic(f);
  RECOG.SetPseudoRandomStamp(g,"ClassicalNatural");

  # First check whether we are applicable:
  if d = 2 then
      if not RECOG.IsThisSL2Natural(GeneratorsOfGroup(g),f) then
          Info(InfoRecog,2,"ClassicalNatural: Is not PSL_2.");
          return fail; # FIXME: fail = TemporaryFailure here really correct?
      fi;
  else
      classical := RecogniseClassical(g);
      if classical.isSLContained <> true then
          Info(InfoRecog,2,"ClassicalNatural: Is not PSL.");
          return fail; # FIXME: fail = TemporaryFailure here really correct?
      fi;
  fi;

  # Now get rid of nasty determinants:
  gens := ShallowCopy(GeneratorsOfGroup(g));
  changed := false;
  z := Z(q);
  gcd := Gcdex(d,q-1);
  for i in [1..Length(gens)] do
      det := DeterminantMat(gens[i]);
      if not IsOne(det) then
          root := RECOG.ComputeRootInFiniteField(det,gcd.gcd,f);
          if root = fail then
              ErrorNoReturn("Should not have happened, 15634, tell Max!");
          fi;
          gens[i] := gens[i] * root;
          changed := true;
      fi;
  od;
  if changed then
      gm := GroupWithMemory(gens);
      pr := ProductReplacer(GeneratorsOfGroup(gm),rec(maxdepth := 500));
      gm!.pseudorandomfunc := [rec( func := Next, args := [pr] )];
  else
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

      # This is (P)SL2, lets set up the recognition:
      Info(InfoRecog,2,"ClassicalNatural: this is PSL_2!");
      if IsEvenInt(q) then
          std := RECOG.RecogniseSL2NaturalEvenChar(gm,f,false);
          ri!.comment := "PSL2Even";
      else
          std := RECOG.RecogniseSL2NaturalOddCharUsingBSGS(gm,f);
          ri!.comment := "PSL2Odd";
      fi;
      Setslptonice(ri,SLPOfElms(std.all));
      ri!.nicebas := std.bas;
      ri!.nicebasi := std.basi;
      SetNiceGens(ri,List(StripMemory(std.all),x->std.basi*x*std.bas));
      ri!.fakegens := RECOG.InitSLfake(f,2);
      ri!.fakegens.count := 0;
      ri!.gcd := gcd;
      SetFilterObj(ri,IsLeaf);
      SetSize(ri,(q+1)*(q-1)*q/GcdInt(2,q-1));
      SetIsRecogInfoForSimpleGroup(ri, q>3);
      Setslpforelement(ri,SLPforElementFuncsProjective.PSL2);
      return Success;
  else   # bigger than 2:
      if classical.isSLContained = true then
          # Do not run the generic code in small cases:
          if (q^d-1)/(q-1) <= 1000 or d = 3 then
              # FIXME: Note d=3 currently has a problem in the SL2-finder.
              Info(InfoRecog,2,"Classical natural: SL(",d,",",q,"): small ",
                   "case, handing over to Schreier-Sims.");
              ri!.comment := Concatenation("SL(",String(d),",",String(q),")",
                                           "_StabilizerChain");
              return FindHomMethodsProjective.StabilizerChainProj(ri,g);
          fi;
          Info(InfoRecog,2,"ClassicalNatural: this is PSL_n!");
          std := RECOG.FindStdGens_SL(gm,f);
          Setslptonice(ri,std.slpstd);
          ri!.nicebas := std.bas;
          ri!.nicebasi := std.basi;
          ext := DegreeOverPrimeField(f);
          stdg := RECOG.MakeSL_StdGens(p,ext,d,d);
          SetNiceGens(ri,List(StripMemory(stdg.all),
                      x->std.basi*x*std.bas));
          ri!.fakegens := RECOG.InitSLfake(f,d);
          ri!.fakegens.count := 0;
          ri!.comment := "PSLd";
          ri!.gcd := gcd;
          SetFilterObj(ri,IsLeaf);
          SetSize(ri,Product([0..d-1],i->(q^d-q^i))/((q-1)*gcd.gcd));
          SetIsRecogInfoForSimpleGroup(ri,true);
          Setslpforelement(ri,SLPforElementFuncsProjective.PSLd);
          return Success;
      fi;
  fi;

  return fail; # FIXME: fail = TemporaryFailure here really correct?

end);
