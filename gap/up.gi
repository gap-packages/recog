SLnUpStep := function(w)
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
  local FixHn,Fixc,Vn,Vnc,c,c1,c1f,can,cf,ci,cii,coeffs,flag,i,id,int1,int2,int3,int4,j,k,lambda,newbas,newbasf,newbasfi,newbasi,newpart,s,sf,slp,std,sum1,tf,trans,transh,transv,v,vals;

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
          Error("this program only works for odd n or n=2");
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
      # newpart := BasisVectors(Basis(int2));
      newpart := ExtractSubMatrix(c,[1..w.n-1],[1..w.d]);
      # Clean out the first n entries to go to the fixed space of SL_n:
      CopySubMatrix(id,newpart,[w.n+1..2*w.n-1],[1..w.n-1],
                               [1..w.n],[1..w.n]);
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

  # Now consider the transvections t_i:
  # t_i : w.bas[j] -> w.bas[j]        for j <> i and
  # t_i : w.bas[i] -> w.bas[i] + ww
  # We want to modify (t_i)^c such that it fixes w.bas{[1..w.n]}:
  trans := [];
  can := CanonicalBasis(w.f);
  std := RECOG.InitSLfake(w.f,w.n);
  for i in [1..w.n-1] do
      # This does t_i
      for lambda in BasisVectors(can) do
          # This does t_i : v_j -> v_j + lambda * v_n
          RECOG.ResetSLstd(std);
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
  transv := [];
  for i in [1..w.n-1] do
      for lambda in BasisVectors(can) do
          tf := trans[1]^0;
          vals := BlownUpVector(can,cii[i]*lambda);
          for j in [1..w.ext * (w.n-1)] do
              tf := tf * trans[j]^IntFFE(vals[j]);
          od;
          Add(transv,tf);
      od;
  od;

  # Now to the "horizontal" transvections, first create them as SLPs:
  transh := [];
  for i in [1..w.n-1] do
      # This does u_i : v_j -> v_j + v_n
      RECOG.ResetSLstd(std);
      RECOG.DoColOp_SL(false,w.n,i,One(w.f),std);
      tf := ResultOfStraightLineProgram(SLPOfElm(std.right),w.slnstdf);
      # Now conjugate with c:
      tf := tf^cf;
      # Now cleanup in rows above row n:
      RECOG.ResetSLstd(std);
      for j in [1..w.n-1] do
          RECOG.DoRowOp_SL(false,j,w.n,-ci[j][w.n],std);
      od;
      tf := ResultOfStraightLineProgram(SLPOfElm(std.left),w.slnstdf)*tf;
      # Now cleanup in rows below row n:
      for j in [1..w.n-1] do
          coeffs := RECOG.FindFFCoeffs(std,-ci[w.n+j][w.n]);
          for k in [1..w.ext] do
              if not(IsZero(coeffs[k])) then
                  tf := transv[(j-1)*w.ext + k]^coeffs[k] * tf;
              fi;
          od;
      od;
      # Now cleanup column n above row n:
      RECOG.ResetSLstd(std);
      for j in [1..w.n-1] do
          RECOG.DoColOp_SL(false,j,w.n,ci[j][w.n],std);
      od;
      tf := tf*ResultOfStraightLineProgram(SLPOfElm(std.right),w.slnstdf);
      # Now cleanup row n left of column n:
      RECOG.ResetSLstd(std);
      for j in [1..w.n-1] do
          RECOG.DoRowOp_SL(false,w.n,j,-c[i][j],std);
      od;
      tf := ResultOfStraightLineProgram(SLPOfElm(std.left),w.slnstdf)*tf;
      # Now cleanup column n below row n:
      for j in [1..w.n-1] do
          coeffs := RECOG.FindFFCoeffs(std,ci[w.n+j][w.n]);
          for k in [1..w.ext] do
              if not(IsZero(coeffs[k])) then
                  tf := tf * transv[(j-1)*w.ext + k]^coeffs[k];
              fi;
          od;
      od;
      Add(transh,tf);
  od;

  # Now put together the n-cycle:
  # 2n-1 -> 2n-2 -> ... -> n+1 -> n -> 2n-1
  flag := false;
  s := One(w.slnstdf[1]);
  for i in [w.n-1,w.n-2..1] do
      if flag then
          # Make [[0,-1],[1,0]] in coordinates w.n and w.n+i:
          tf := transv[(i-1)*w.ext+1]*transh[i]^-1*transv[(i-1)*w.ext+1];
      else
          # Make [[0,1],[-1,0]] in coordinates w.n and w.n+i:
          tf := transv[(i-1)*w.ext+1]^-1*transh[i]*transv[(i-1)*w.ext+1]^-1;
      fi;
      s := s * tf;
      flag := not(flag);
  od;

  # Finally put together the new 2n-1-cycle and 2n-2-cycle:
  w.slnstdf[2*w.ext+1] := w.slnstdf[2*w.ext+1] * s;
  w.slnstdf[2*w.ext+2] := w.slnstdf[2*w.ext+2] * s;

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

MakeTest := function(p,e,n,d)
  local a,fake,q,r;
  q := p^e;
  a := RECOG.MakeSL_StdGens(p,e,n,d).all;
  Append(a,GeneratorsOfGroup(SL(d,q)));
  a := GeneratorsWithMemory(a);
  fake := GeneratorsWithMemory(List([1..Length(a)],i->()));
  r := rec( f := GF(q), d := d, n := n, bas := IdentityMat(d,GF(q)),
            basi := IdentityMat(d,GF(q)), sld := Group(a),
            sldf := fake, slnstdf := fake{[1..2*e+2]}, p := p, ext := e );
  return r;
end;

