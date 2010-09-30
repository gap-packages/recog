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
local ActHn,FixHn,I1,I2,c,c1,c1f,cf,i,id,int1,int3,int4,int5,newbas,newbasi,s,sc1,sc1f,sf,slp,std,sum2;

  Info(InfoRecog,3,"Going up: ",w.n," (",w.d,")...");

  # We already have an SLP for an n-1-cycle: it is one of the std gens.
  # For n=2 we use a transvection for this purpose.

  # We compute exclusively in our basis, so we occasionally need an
  # identity matrix:
  id := IdentityMat(w.d,w.f);
  FixHn := VectorSpace(w.f,id{[w.n+1..w.d]});
  ActHn := VectorSpace(w.f,id{[1..w.n]});

  # Find a good random element:
  while true do    # will be left by break
      Print(".\c");
      c1 := PseudoRandom(w.sld);
      slp := SLPOfElm(c1);
      c1f := ResultOfStraightLineProgram(slp,w.sldf);
      # Do the base change into our basis:
      c1 := w.bas * c1 * w.basi;
      I1 := VectorSpace(w.f,c1{Concatenation([1],[w.n+1..w.d])});
      I2 := VectorSpace(w.f,c1{[2..w.n]});
      int1 := Intersection(I1,FixHn);
      if not(Dimension(int1) = w.d - (2 * w.n - 1)) then 
          Print("1\c"); continue;
      fi;
      sum2 := ClosureLeftModule(I2,ActHn);
      if not(Dimension(sum2) = 2 * w.n - 1) then 
          Print("2\c"); continue;
      fi;
      int3 := Intersection(I1,ActHn);   # necessary???
      if not(Dimension(int3) = 1) then 
          Print("3\c"); continue;
      fi;
      int4 := Intersection(FixHn,sum2);
      int5 := Intersection(int4,I1);
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
  cf := sf^c1f;
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
  v := int1[1];
  ww := v*c^-1;
  
  # Replace the n-th basis vector in the basis by v:
  newbas := MutableCopyMat(id);
  newbas[w.n] := v;
  newbasi := newbas^-1;
  w.bas := newbas * w.bas;
  w.basi := w.basi * newbasi;
  c := newbas * c * newbasi;


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

