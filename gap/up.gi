SL2UpStep := function(w)
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
  #   p       : characteristic
  #   ext     : q=p^ext
  #
  # We keep the following invariants (going from n -> n':=2n-1)
  #   bas, basi is a base change to the target base
  #   slnstdf are SLPs to reach standard generators of SL_n from the
  #       generators of sld
local FixHn,I2,Vn,Vnc,c,c1,c1f,cf,ci,i,id,int1,int3,int4,int5,newbas,newbasf,newbasfi,newbasi,s,sc1,sc1f,sf,slp,std,sum2,v,ww;

  Info(InfoRecog,3,"Going up: ",w.n," (",w.d,")...");

  # We already have an SLP for an n-1-cycle: it is one of the std gens.
  # For n=2 we use a transvection for this purpose.

  # We compute exclusively in our basis, so we occasionally need an
  # identity matrix:
  id := IdentityMat(w.d,w.f);
  FixHn := VectorSpace(w.f,id{[w.n+1..w.d]});
  Vn := VectorSpace(w.f,id{[1..w.n]});

  # Find a good random element:
  while true do    # will be left by break
      Print(".\c");
      c1 := PseudoRandom(w.sld);
      slp := SLPOfElm(c1);
      c1f := ResultOfStraightLineProgram(slp,w.sldf);
      # Do the base change into our basis:
      c1 := w.bas * c1 * w.basi;
      Vnc := VectorSpace(w.f,c1{Concatenation([1],[w.n+1..w.d])});
      I2 := VectorSpace(w.f,c1{[2..w.n]});
      int1 := Intersection(Vnc,FixHn);
      if not(Dimension(int1) = w.d - (2 * w.n - 1)) then 
          Print("1\c"); continue;
      fi;
      sum2 := ClosureLeftModule(I2,Vn);
      if not(Dimension(sum2) = 2 * w.n - 1) then 
          Print("2\c"); continue;
      fi;
      int3 := Intersection(Vnc,Vn);   # necessary???
      if not(Dimension(int3) = 1) then 
          Print("3\c"); continue;
      fi;
      int4 := Intersection(FixHn,sum2);
      int5 := Intersection(int4,Vnc);
      if not(Dimension(int5) = 0) then 
          Print("4\c"); continue;
      fi;
      break;   # all conditions met
  od;
  Print(" found c1.\n");

  # Change basis:
  newbas := Concatenation(id{[1..w.n]},c1{[2..w.n]},BasisVectors(Basis(int1)));
  ConvertToMatrixRep(newbas,Size(w.f));
  # Zero out first n components of new basis vectors:
  CopySubMatrix(id,newbas,[w.n+1..2*w.n-1],[w.n+1..2*w.n-1],
                          [1..w.n],[1..w.n]);
  newbasi := newbas^-1;
  w.bas := newbas * w.bas;
  w.basi := w.basi * newbasi;
  c1 := newbas * c1 * newbasi;
  # Now SL_n should still be nice!

  # Make some standard generators to compute:
  std := RECOG.MakeSL_StdGens(w.p,w.ext,w.n,w.d).all;

  # Find good short word:
  if w.n > 2 then
      s := id{Concatenation([1],[3..w.n],[2],[w.n+1..w.d])};
      ConvertToMatrixRepNC(s,w.f);
      if IsOddInt(w.n) then s[w.n] := -s[w.n]; fi;
      sf := w.slnstdf[2*w.ext+2];
  else
      # In this case the n-1-cycle is the identity, so we take a transvection:
      s := MutableCopyMat(id);
      s[1][2] := One(w.f);
      sf := w.slnstdf[1];
  fi;
  sc1 := s^c1;
  sc1f := sf^c1f;
  c := sc1;
  cf := sc1f;
  Error(-1);
  while true do   # will be left by break
      Print("#\c");
      int1 := SumIntersectionMat(id{[1..w.n]},c{[1..w.n]})[2];
      if Length(int1) = 1 and not(IsZero(int1[1][w.n])) 
          then break; fi;
      i := Random(1,Length(std));
      c := c * std[i] * sc1;
      cf := cf * w.slnstdf[i] * sc1f;
  od;

  # Now we have our conjugating element, it maps some vector in the
  # original acting space back into that space.
  v := int1[1]/int1[1][w.n];   # normalize to 1 in position n
  ww := v*c^-1;
  
  Error(0);
  # Replace the n-th basis vector in the basis by v:
  newbas := MutableCopyMat(id);
  newbas[w.n] := v;
  newbasi := newbas^-1;
  # Now write this matrix newbas as an SLP in the standard generators
  # of our SL_n. Then we know which generators to take for our new
  # standard generators, namely newbas^-1 * std * newbas.
  newbasf := RECOG.InitSLfake(w.f,w.n);
  for i in [1..w.n-1] do
      if not(IsZero(v[i])) then
          RECOG.DoColOp_SL(false,w.n,i,v[i],newbasf);
      fi;
  od;
  newbasf := ResultOfStraightLineProgram(SLPOfElm(newbasf.right),
                                         w.slnstdf);
  newbasfi := newbasf^-1;
  w.slnstdf := List(w.slnstdf,x->newbasfi * x * newbasf);
  w.bas := newbas * w.bas;
  w.basi := w.basi * newbasi;
  c := newbas * c * newbasi;
  # Now consider the transvections t_i:
  # t_i : w.bas[j] -> w.bas[j]        for j <> i and
  # t_i : w.bas[i] -> w.bas[i] + ww
  # We want to modify (t_i)^c such that it fixes w.bas{[1..w.n]}:
  ci := c^-1;   # this tells us 
  #

Error(1);

  return w;
end;

SL2UpStepTry2 := function(w)
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
  #   p       : characteristic
  #   ext     : q=p^ext
  #
  # We keep the following invariants (going from n -> n':=2n-1)
  #   bas, basi is a base change to the target base
  #   slnstdf are SLPs to reach standard generators of SL_n from the
  #       generators of sld
local FixHn,Fixc,Vn,Vnc,c,c1,c1f,can,cf,ci,cii,i,id,int1,int2,int3,int4,j,lambda,newbas,newbasf,newbasfi,newbasi,newpart,s,sf,slp,std,sum1,tf,trans,trans2,v,vals;

  Info(InfoRecog,3,"Going up: ",w.n," (",w.d,")...");

  # We compute exclusively in our basis, so we occasionally need an
  # identity matrix:
  id := IdentityMat(w.d,w.f);
  FixHn := VectorSpace(w.f,id{[w.n+1..w.d]});
  Vn := VectorSpace(w.f,id{[1..w.n]});

  # First pick an element in SL_n with fixed space of dimension d-n+1:
  # We already have an SLP for an n-1-cycle: it is one of the std gens.
  # For n=2 we use a transvection for this purpose.
  if w.n > 2 then
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
      # In this case the n-1-cycle is the identity, so we take a transvection:
      s := MutableCopyMat(id);
      s[1][2] := One(w.f);
      sf := w.slnstdf[1];
  fi;

  # Find a good random element:
  w.count := 0;
  while true do   # will be left by break
      while true do    # will be left by break
          Print(".\c");
          w.count := w.count + 1;
          c1 := PseudoRandom(w.sld);
          slp := SLPOfElm(c1);
          c1f := ResultOfStraightLineProgram(slp,w.sldf);
          # Do the base change into our basis:
          c1 := w.bas * c1 * w.basi;
          c := s^c1;
          cf := sf^c1f;
          # Now check that Vn + Vn*s^c1 has dimension 2n-1:
          Vnc := VectorSpace(w.f,c{[1..w.n]});
          sum1 := ClosureLeftModule(Vn,Vnc);
          if Dimension(sum1) = 2*w.n - 1 then 
              int1 := Intersection(Vnc,Vn);
              Assert(0,Dimension(int1)=1);
              v := Basis(int1)[1];
              if IsZero(v[w.n]) then continue; fi;
              v := v / v[w.n];   # normalize to 1 in position n
              Assert(0,v*c=v);
              ci := c^-1;
              break;
          fi;
      od;

      # Now we found our 2n-1-dimensional space W. Since SL_n
      # has a d-n-dimensional fixed space W_{d-n} and W contains a complement
      # of that fixed space, the intersection of W and W_{d-n} has dimension n-1.
      # Change basis:
      int2 := Intersection(FixHn, sum1);
      Fixc := VectorSpace(w.f,NullspaceMat(c-One(c)));
      int4 := Intersection(Fixc,int2);
      if Dimension(int4) > 0 then
          Print("Ooops, Fixc intersects int2!\n");
          continue;
      fi;
      newpart := BasisVectors(Basis(int2));
      newbas := Concatenation(id{[1..w.n-1]},[v],newpart);
      int3 := Intersection(FixHn,Fixc);
      Assert(0,Dimension(int3)=w.d-2*w.n+1);
      Append(newbas,BasisVectors(Basis(int3)));
      ConvertToMatrixRep(newbas,Size(w.f));
      newbasi := newbas^-1;
      ci := newbas * ci * newbasi;
      cii := ExtractSubMatrix(ci,[w.n+1..2*w.n-1],[1..w.n-1]);
      ConvertToMatrixRep(cii,Size(w.f));
      cii := cii^-1;
      if cii <> fail then 
          c := newbas * c * newbasi;
          w.bas := newbas * w.bas;
          w.basi := w.basi * newbasi;
          break; 
      fi;
      Print("Ooops, no nice bottom...\n");
      # Otherwise simply try again
  od;
  Print(" found c1 and c.\n");
  # Now SL_n has to be repaired according to the base change newbas:

  # Make some standard generators to compute:
  std := RECOG.MakeSL_StdGens(w.p,w.ext,w.n,w.d).all;

  # Now write this matrix newbas as an SLP in the standard generators
  # of our SL_n. Then we know which generators to take for our new
  # standard generators, namely newbas^-1 * std * newbas.
  newbasf := RECOG.InitSLfake(w.f,w.n);
  for i in [1..w.n-1] do
      if not(IsZero(v[i])) then
          RECOG.DoColOp_SL(false,w.n,i,v[i],newbasf);
      fi;
  od;
  newbasf := ResultOfStraightLineProgram(SLPOfElm(newbasf.right),
                                         w.slnstdf);
  newbasfi := newbasf^-1;
  w.slnstdf := List(w.slnstdf,x->newbasfi * x * newbasf);
  #Unbind(newbasf); Unbind(newbasfi); Unbind(newbas); Unbind(newbasi);

  # Now consider the transvections t_i:
  # t_i : w.bas[j] -> w.bas[j]        for j <> i and
  # t_i : w.bas[i] -> w.bas[i] + ww
  # We want to modify (t_i)^c such that it fixes w.bas{[1..w.n]}:
  trans := [];
  can := CanonicalBasis(w.f);
  for i in [1..w.n-1] do
      trans2 := [];
      # This does t_i
      for lambda in BasisVectors(can) do
          # This does t_i : v_j -> v_j + lambda * v_n
          std := RECOG.InitSLfake(w.f,w.n);
          RECOG.DoRowOp_SL(false,i,w.n,lambda,std);
          tf := ResultOfStraightLineProgram(SLPOfElm(std.left),w.slnstdf);
          # Now conjugate with c:
          tf := tf^cf;
          # Now cleanup in column n above row n, the entries there
          # are lambda times the stuff in column i of ci:
          RECOG.ResetSLstd(std);
          for j in [1..w.n-1] do
              RECOG.DoRowOp_SL(false,j,w.n,-ci[j][i]*lambda,std);
          od;
          tf := ResultOfStraightLineProgram(SLPOfElm(std.left),w.slnstdf)*tf;
          Add(trans,tf);
      od;
  od;
  # Now put together the clean ones by our knowledge of c^-1:
  cii := TransposedMat(cii);
  trans2 := [];
  for i in [1..w.n-1] do
      for lambda in BasisVectors(can) do
          tf := trans[1]^0;
          vals := BlownUpVector(can,cii[i]*lambda);
          Error(2);
          for j in [1..w.ext * (w.n-1)] do
              tf := tf * trans[j]^IntFFE(vals[j]);
          od;
          Add(trans2,tf);
      od;
  od;

Error(1);

  return w;
end;

MakeSituation := function(p,e,n,d)
  local a,q,r;
  q := p^e;
  a := RECOG.MakeSL_StdGens(p,e,n,d).all;
  Append(a,GeneratorsOfGroup(SL(d,q)));
  a := GeneratorsWithMemory(a);
  r := rec( f := GF(q), d := d, n := n, bas := IdentityMat(d,GF(q)),
            basi := IdentityMat(d,GF(q)), sld := Group(a),
            sldf := a, slnstdf := a{[1..2*e+2]}, p := p, ext := e );
  return r;
end;

