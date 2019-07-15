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
  local DoColOp_n,DoRowOp_n,FixSLn,Fixc,MB,Vn,Vnc,aimdim,c,c1,c1f,cf,cfi,ci,cii,coeffs,flag,i,id,int1,int3,j,k,lambda,list,mat,newbas,newbasf,newbasfi,newbasi,newdim,newpart,perm,pivots,pivots2,pos,pow,s,sf,slp,std,sum1,tf,trans,transd,transr,v,vals,zerovec;

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
  aimdim := Minimum(2*w.n-1,w.d);
  newdim := aimdim - w.n;
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
          if Dimension(sum1) = aimdim then
              Fixc := VectorSpace(w.f,NullspaceMat(c-One(c)));
              int1 := Intersection(Fixc,Vn);
              for i in [1..Dimension(int1)] do
                  v := Basis(int1)[i];
                  if not IsZero(v[w.n]) then break; fi;
              od;
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
          Assert(0,Dimension(int3)=w.d-2*w.n+1);
          Append(newbas,BasisVectors(Basis(int3)));
      fi;
      ConvertToMatrixRep(newbas,Size(w.f));
      newbasi := newbas^-1;
      if newbasi = fail then
          Print("Ooops, Fixc intersected too much, we try again\n");
          continue;
      fi;
      ci := newbas * ci * newbasi;
      cii := ExtractSubMatrix(ci,[w.n+1..aimdim],[1..w.n-1]);
      ConvertToMatrixRep(cii,Size(w.f));
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
      Print("Ooops, no nice bottom...\n");
      # Otherwise simply try again
  od;
  Print(" found c1 and c.\n");
  # Now SL_n has to be repaired according to the base change newbas:

# Error(1);

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

# Error(2);

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
              tf := DoRowOp_n(tf,j,w.n,-ci[j][i]*lambda,w);
          od;
          Add(trans,tf);
      od;
  od;

# Error(3);

  # Now put together the clean ones by our knowledge of c^-1:
  transd := [];
  for i in pivots2 do
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

# Error(4);

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
          tf := DoRowOp_n(tf,j,w.n,-ci[j][w.n],w);
      od;
      # Now cleanup in rows below row n:
      for j in [1..newdim] do
          coeffs := IntVecFFE(Coefficients(w.can,-ci[w.n+j][w.n]));
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
          tf := DoColOp_n(tf,j,w.n,ci[j][w.n],w);
      od;
      # Now cleanup row n left of column n:
      for j in [1..w.n-1] do
          tf := DoRowOp_n(tf,w.n,j,-c[i][j],w);
      od;
      # Now cleanup column n below row n:
      for j in [1..newdim] do
          coeffs := IntVecFFE(Coefficients(w.can,ci[w.n+j][w.n]));
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

# Error(5);

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

guck :=
function ( w )
    local  i;
    for i  in w.slnstdf  do
        Display( w.bas * i * w.basi );
    od;
    if IsBound( w.transh )  then
        for i  in [ 1 .. Length( w.transh ) ]  do
            Print( i, "\n" );
            if IsBound(w.transh[i]) then
                Display( w.bas * w.transh[i] * w.basi );
            fi;
        od;
    fi;
    if IsBound( w.transv )  then
        for i  in [ 1 .. Length( w.transv ) ]  do
            Print( i, "\n" );
            if IsBound(w.transv[i]) then
                Display( w.bas * w.transv[i] * w.basi );
            fi;
        od;
    fi;
    return;
end;

