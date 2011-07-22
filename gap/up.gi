RECOG.LinearAction := function(bas,field,el)
  local mat,vecs;
  vecs := BasisVectors(bas);
  mat := List(vecs,v->Coefficients(bas,v*el));
  ConvertToMatrixRep(mat,field);
  return mat;
end;

SLnUpStep := function(w)
  # w has components:
  #   d       : size of big SL
  #   n       : size of small SL
  #   slnstdf : fakegens for SL_n standard generators
  #   transh  : fakegens for the "horizontal" transvections n,i for 1<=i<=n-1
  #             entries can be unbound in which case they are made from slnstdf
  #   transv  : fakegens for the "vertical" transvections i,n for 1<=i<=n-1
  #             entries can be unbound in which case they are made from slnstdf
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
  #
  # We keep the following invariants (going from n -> n':=2n-1)
  #   bas, basi is a base change to the target base
  #   slnstdf are SLPs to reach standard generators of SL_n from the
  #       generators of sld
  local DoColOp_n,DoRowOp_n,FixSLn,Fixc,Vn,Vnc,c,c1,c1f,cf,cfi,ci,cii,coeffs,flag,i,id,int1,int2,int3,int4,j,k,lambda,newbas,newbasf,newbasfi,newbasi,newpart,pos,pow,s,sf,slp,std,sum1,tf,trans,transd,transr,v,vals;

  Info(InfoRecog,3,"Going up: ",w.n," (",w.d,")...");

  # Before we begin, we upgrade the data structure with a few internal
  # things:

  if not(IsBound(w.can)) then w.can := CanonicalBasis(w.f); fi;
  if not(IsBound(w.canb)) then w.canb := BasisVectors(w.can); fi;
  if not(IsBound(w.One)) then w.One := One(w.slnstdf[1]); fi;
  if not(IsBound(w.transh)) then w.transh := []; fi;
  if not(IsBound(w.transv)) then w.transv := []; fi;
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
          if not(IsBound(w.transh[pos])) then
              RECOG.ResetSLstd(std);
              RECOG.DoColOp_SL(false,w.n,i,w.canb[k],std);
              w.transh[pos] := std.right;
          fi;
          if not(IsBound(w.transv[pos])) then
              RECOG.ResetSLstd(std);
              RECOG.DoRowOp_SL(false,i,w.n,w.canb[k],std);
              w.transv[pos] := std.left;
          fi;
      od;
  od;
  Unbind(std);
Error(0);

  # Now we can define two helper functions:
  DoColOp_n := function(el,i,j,lambda,w)
    # This adds lambda times the i-th column to the j-th column.
    # Note that either i or j must be equal to n!
    local coeffs,k;
    coeffs := IntVecFFE(Coefficients(w.can,lambda));
    if i = w.n then
        for k in [1..w.ext] do
            if not(IsZero(coeffs[k])) then
                if IsOne(coeffs[k]) then
                    el := el * w.transh[(j-1)*w.ext+k];
                else
                    el := el * w.transh[(j-1)*w.ext+k]^coeffs[k];
                fi;
            fi;
        od;
    elif j = w.n then
        for k in [1..w.ext] do
            if not(IsZero(coeffs[k])) then
                if IsOne(coeffs[k]) then
                    el := el * w.transv[(i-1)*w.ext+k];
                else
                    el := el * w.transv[(i-1)*w.ext+k]^coeffs[k];
                fi;
            fi;
        od;
    else
        Error("either i or j must be equal to n");
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
            if not(IsZero(coeffs[k])) then
                if IsOne(coeffs[k]) then
                    el := w.transv[(i-1)*w.ext+k] * el;
                else
                    el := w.transv[(i-1)*w.ext+k]^coeffs[k] * el;
                fi;
            fi;
        od;
    elif i = w.n then
        for k in [1..w.ext] do
            if not(IsZero(coeffs[k])) then
                if IsOne(coeffs[k]) then
                    el := w.transh[(j-1)*w.ext+k] * el;
                else
                    el := w.transh[(j-1)*w.ext+k]^coeffs[k] * el;
                fi;
            fi;
        od;
    else
        Error("either i or j must be equal to n");
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
          cfi := cf^-1;
          # Now check that Vn + Vn*s^c1 has dimension 2n-1:
          Vnc := VectorSpace(w.f,c{[1..w.n]});
          sum1 := ClosureLeftModule(Vn,Vnc);
          if Dimension(sum1) = 2*w.n - 1 then 
              int1 := Intersection(Vnc,Vn);
              Assert(0,Dimension(int1)=1);
              v := Basis(int1)[1];
              if IsZero(v[w.n]) then 
                  Print("Ooops: Component n was zero!\n");
                  continue; 
              fi;
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
      int2 := Intersection(FixSLn, sum1);
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
      int3 := Intersection(FixSLn,Fixc);
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

Error(1);

  # Now write this matrix newbas as an SLP in the standard generators
  # of our SL_n. Then we know which generators to take for our new
  # standard generators, namely newbas^-1 * std * newbas.
  newbasf := w.One;
  for i in [1..w.n-1] do
      if not(IsZero(v[i])) then
          newbasf := DoColOp_n(newbasf,w.n,i,v[i],w);
          # was: RECOG.DoColOp_SL(false,w.n,i,v[i],newbasf);
      fi;
  od;
  # was: newbasf := ResultOfStraightLineProgram(SLPOfElm(newbasf.right),
  #                                             w.slnstdf);
  newbasfi := newbasf^-1;
  w.slnstdf := List(w.slnstdf,x->newbasfi * x * newbasf);
  # Now update caches:
  w.transh := List(w.transh,x->newbasfi * x * newbasf);
  w.transv := List(w.transv,x->newbasfi * x * newbasf);

Error(2);

  # Now consider the transvections t_i:
  # t_i : w.bas[j] -> w.bas[j]        for j <> i and
  # t_i : w.bas[i] -> w.bas[i] + ww
  # We want to modify (t_i)^c such that it fixes w.bas{[1..w.n]}:
  trans := [];
  # was: std := RECOG.InitSLfake(w.f,w.n);
  for i in [1..w.n-1] do
      # This does t_i
      for lambda in w.canb do
          # This does t_i : v_j -> v_j + lambda * v_n
          tf := w.One;
          tf := DoRowOp_n(tf,i,w.n,lambda,w);
          # was: RECOG.ResetSLstd(std);
          # was: RECOG.DoRowOp_SL(false,i,w.n,lambda,std);
          # was: tf:=ResultOfStraightLineProgram(SLPOfElm(std.left),w.slnstdf);
          # Now conjugate with c:
          tf := cfi*tf*cf;
          # Now cleanup in column n above row n, the entries there
          # are lambda times the stuff in column i of ci:
          # was: RECOG.ResetSLstd(std);
          for j in [1..w.n-1] do
              tf := DoRowOp_n(tf,j,w.n,-ci[j][i]*lambda,w);
              # was: RECOG.DoRowOp_SL(false,j,w.n,-ci[j][i]*lambda,std);
          od;
          # was: 
          # tf:=ResultOfStraightLineProgram(SLPOfElm(std.left),w.slnstdf)*tf;
          Add(trans,tf);
      od;
  od;

Error(3);

  # Now put together the clean ones by our knowledge of c^-1:
  cii := TransposedMat(cii);
  transd := [];
  for i in [1..w.n-1] do
      for lambda in w.canb do
          tf := w.One;
          vals := BlownUpVector(w.can,cii[i]*lambda);
          for j in [1..w.ext * (w.n-1)] do
              pow := IntFFE(vals[j]);
              if not(IsZero(pow)) then
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

Error(4);

  # Now to the "horizontal" transvections, first create them as SLPs:
  transr := [];
  for i in [1..w.n-1] do
      # This does u_i : v_j -> v_j + v_n
      tf := w.One;
      tf := DoColOp_n(tf,w.n,i,One(w.f),w);
      # was: RECOG.ResetSLstd(std);
      # was: RECOG.DoColOp_SL(false,w.n,i,One(w.f),std);
      # was: tf := ResultOfStraightLineProgram(SLPOfElm(std.right),w.slnstdf);
      # Now conjugate with c:
      #Error("A");
      tf := cfi*tf*cf;
      #Error("a");
      # Now cleanup in rows above row n:
      # was: RECOG.ResetSLstd(std);
      for j in [1..w.n-1] do
          tf := DoRowOp_n(tf,j,w.n,-ci[j][w.n],w);
          # was: RECOG.DoRowOp_SL(false,j,w.n,-ci[j][w.n],std);
      od;
      #Error("b");
      # was: tf := ResultOfStraightLineProgram(SLPOfElm(std.left),w.slnstdf)*tf;
      # Now cleanup in rows below row n:
      for j in [1..w.n-1] do
          coeffs := IntVecFFE(Coefficients(w.can,-ci[w.n+j][w.n]));
          # was: coeffs := RECOG.FindFFCoeffs(std,-ci[w.n+j][w.n]);
          for k in [1..w.ext] do
              if not(IsZero(coeffs[k])) then
                  if IsOne(coeffs[k]) then
                      tf := transd[(j-1)*w.ext + k] * tf;
                  else
                      tf := transd[(j-1)*w.ext + k]^coeffs[k] * tf;
                  fi;
              fi;
          od;
      od;
      #Error("c");
      # Now cleanup column n above row n:
      # was: RECOG.ResetSLstd(std);
      for j in [1..w.n-1] do
          tf := DoColOp_n(tf,j,w.n,ci[j][w.n],w);
          # was: RECOG.DoColOp_SL(false,j,w.n,ci[j][w.n],std);
      od;
      # was: 
      # tf := tf*ResultOfStraightLineProgram(SLPOfElm(std.right),w.slnstdf);
      #Error("d");
      # Now cleanup row n left of column n:
      # was: RECOG.ResetSLstd(std);
      for j in [1..w.n-1] do
          tf := DoRowOp_n(tf,w.n,j,-c[i][j],w);
          # was: RECOG.DoRowOp_SL(false,w.n,j,-c[i][j],std);
      od;
      # was: tf := ResultOfStraightLineProgram(SLPOfElm(std.left),w.slnstdf)*tf;
      #Error("e");
      # Now cleanup column n below row n:
      for j in [1..w.n-1] do
          coeffs := IntVecFFE(Coefficients(w.can,ci[w.n+j][w.n]));
          # was: coeffs := RECOG.FindFFCoeffs(std,ci[w.n+j][w.n]);
          for k in [1..w.ext] do
              if not(IsZero(coeffs[k])) then
                  if IsOne(coeffs[k]) then
                      tf := tf * transd[(j-1)*w.ext + k];
                  else
                      tf := tf * transd[(j-1)*w.ext + k]^coeffs[k];
                  fi;
              fi;
          od;
      od;
      #Error("f");
      Add(transr,tf);
  od;

Error(5);

  # Now put together the n-cycle:
  # 2n-1 -> 2n-2 -> ... -> n+1 -> n -> 2n-1
  flag := false;
  s := One(w.slnstdf[1]);
  for i in [w.n-1,w.n-2..1] do
      if flag then
          # Make [[0,-1],[1,0]] in coordinates w.n and w.n+i:
          tf := transd[(i-1)*w.ext+1]*transr[i]^-1*transd[(i-1)*w.ext+1];
      else
          # Make [[0,1],[-1,0]] in coordinates w.n and w.n+i:
          tf := transd[(i-1)*w.ext+1]^-1*transr[i]*transd[(i-1)*w.ext+1]^-1;
      fi;
      s := s * tf;
      flag := not(flag);
  od;

Error(6);

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

