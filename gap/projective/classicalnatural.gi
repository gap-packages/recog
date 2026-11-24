#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This file's authors include Max Neunhöffer, Ákos Seress.
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

# Now the code for writing SLPs:

# Returns a scalar multiple of the matrix y with entries in the field f, or
# fail if there is none. A projective element can reach a node with a scalar
# from a larger field than that of the node.
RECOG.ScaleMatrixIntoField := function(y,f)
  local pos;
  pos := PositionNonZeroInRow(y,1);
  if not y[1,pos] in f then
      y := y[1,pos]^-1 * y;
  fi;
  if not IsSubset(f,FieldOfMatrixList([y])) then
      return fail;
  fi;
  return y;
end;

SLPforElementFuncsProjective.PSL2 := function(ri,x)
  local det,pos,root,s,slp,y;
  ri!.fakegens.count := ri!.fakegens.count + 1;
  if ri!.fakegens.count > 1000 then
      ri!.fakegens := RECOG.InitSLfake(ri!.field,2);
      ri!.fakegens.count := 0;
  fi;
  y := ri!.nicebas * x * ri!.nicebasi;
  y := RECOG.ScaleMatrixIntoField(y,ri!.field);
  if y = fail then
      return fail;
  fi;
  det := DeterminantMat(y);
  if not IsOne(det) then
      # In the projective image, det only has to be a square. If it is not,
      # then the PSL2 recognition path was too optimistic for this element.
      root := RootFFE(ri!.field,1/det,2);
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
  pos := PositionNonZeroInRow(y, 1);
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


# Express an element of PSL_d as an slp in terms of the standard generators
# of RECOG.ClassicalStandardGenerators.
SLPforElementFuncsProjective.PSLd := function(ri,x)
  local det,pos,root,s,slp,y;
  ri!.rewrite.count := ri!.rewrite.count + 1;
  if ri!.rewrite.count > 1000 then
      ri!.rewrite := RECOG.SL_RewriteSetup(ri!.dimension,ri!.field);
  fi;
  y := ri!.nicebas * x * ri!.nicebasi;
  y := RECOG.ScaleMatrixIntoField(y,ri!.field);
  if y = fail then
      return fail;
  fi;
  det := DeterminantMat(y);
  if not IsOne(det) then
      # At this point, y is in the kernel of the determinant map *mod scalars*.
      # That means that det may not be 1 -- it can be any d-th power.
      # We thus can compute a d-th root of 1/det, and scale y with it,
      # in order to obtain a matrix with determinant 1 in the same
      # projective class.
      root := RootFFE(ri!.field,1/det,Length(y));
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
  pos := PositionNonZeroInRow(y, 1);
  s := RECOG.NormaliseScalarForPSLd(y[1,pos],ri!.normlist);
  slp := RECOG.SL_Rewrite(ri!.rewrite,s * y);
  return slp;
end;

# The scalar c with <g> J (g^frob)^T = c J for the form record <form>
# with Gram matrix J, or fail if there is none
RECOG.SimilarityFactor := function(g,form)
  local J,M,pos,c;
  J := form.gram;
  M := g * J * TransposedMat(RECOG.FormConjugate(form,g));
  pos := PositionNonZero(J[1]);
  c := M[1,pos] / J[1,pos];
  if M <> c * J then
      return fail;
  fi;
  return c;
end;

# The spinor norm of the isometry <g> of the symmetric bilinear form beta
# of the form record <form>, q odd, as 0 (a square in form.field, which may
# be larger than the field of the entries of g) or 1. It is the
# discriminant of the Wall form chi(w(1-g), v) = beta(w, v) on the image of
# g - 1 (D. E. Taylor, The geometry of the classical groups, 1992, (11.31)),
# a homomorphism on the whole isometry group (op. cit., Theorem 11.50).
# For a basis x_i(g-1) of the image, of dimension k, chi has matrix -M^T
# with M = beta(x_i(g-1), x_j). Scaling the Gram matrix by c multiplies the
# discriminant by c^k; on SO, k is even.
RECOG.SpinorNorm := function(g,form)
  local sem,k,det;
  sem := SemiEchelonMatTransformation(g - One(g));
  k := Length(sem.vectors);
  if k = 0 then
      return 0;
  fi;
  det := (-1)^k * DeterminantMat(sem.vectors * form.gram
                                 * TransposedMat(sem.coeffs));
  if RECOG.IsSquareFFE(det,Size(form.field)) then
      return 0;
  fi;
  return 1;
end;

# Whether the isometry <g> of determinant 1 of the form record <form> lies
# in Omega (Taylor, op. cit., Theorem 11.51).
RECOG.HasTrivialSpinorNorm := {g,form} -> RECOG.SpinorNorm(g,form) = 0;

# Whether the isometry <g> of the quadratic form of <form>, q even, lies
# in Omega: whether its Dickson invariant, the dimension of the image of
# g - 1 mod 2, is 0 (Taylor, op. cit., p. 160 and Theorem 11.51)
RECOG.HasTrivialDicksonInvariant := g -> IsEvenInt(RankMat(g - One(g)));

# Whether the isometry <g> of the polar form of the quadratic form of
# <form>, q even, preserves the quadratic form: Q o g - Q is then the square
# of a linear form, which vanishes if it does on the basis vectors
RECOG.PreservesQuadraticForm := function(g,form)
  local gA;
  gA := g * form.quad;
  return ForAll([1..NrRows(g)], k -> gA[k] * g[k] = form.quad[k,k]);
end;

# The scalar lambda with lambda <g> in the group of type <type>, "Sp",
# "SU" or an orthogonal type, of the form record <form>, or fail if there
# is none. For "Sp" and the orthogonal types, lambda^2 inverts the
# similarity factor mu, and for the latter lambda g lies in Omega. For q
# even, lambda is unique, and lambda g must preserve the quadratic form if
# form has one. For "SU", mu lies in GF(q0), lambda^(q0+1) inverts it, and
# lambda^d det(g) = 1.
RECOG.ClassicalNaturalScalar := function(type,g,form)
  local f,mu,det,z,q0,lambda,c,t;
  f := form.field;
  mu := RECOG.SimilarityFactor(g,form);
  if mu = fail then
      return fail;
  elif type in RECOG.OrthogonalTypes and IsEvenInt(Size(f)) then
      lambda := RootFFE(f,mu^-1,2);
      if IsBound(form.quad)
         and not RECOG.PreservesQuadraticForm(lambda * g,form) then
          return fail;
      elif not RECOG.HasTrivialDicksonInvariant(lambda * g) then
          return fail;
      fi;
      return lambda;
  elif type = "Sp" then
      if IsOne(mu) then
          return One(f);
      fi;
      return RootFFE(f,mu^-1,2);
  elif type in RECOG.OrthogonalTypes then
      lambda := One(f);
      if not IsOne(mu) then
          lambda := RootFFE(f,mu^-1,2);
          if lambda = fail then
              return fail;
          fi;
      fi;
      # det(-g) = -det(g) for d odd; -1 has spinor norm 1 or not
      for c in [lambda,-lambda] do
          if IsOne(DeterminantMat(c * g))
             and RECOG.HasTrivialSpinorNorm(c * g,form) then
              return c;
          fi;
      od;
      return fail;
  fi;
  det := DeterminantMat(g);
  if IsOne(mu) and IsOne(det) then
      return One(f);
  fi;
  # z^(q0+1) generates GF(q0)^*, and z^(q0-1) the scalars of GU
  z := PrimitiveRoot(f);
  q0 := form.frob;
  lambda := z^(LogFFE(mu^-1,z) / (q0+1));
  c := LogFFE((lambda^NrRows(g) * det)^-1,z^(q0-1));
  t := QuotientMod(c,NrRows(g),q0+1);
  if t = fail then
      return fail;
  fi;
  return lambda * z^((q0-1) * t);
end;

# The image of <g> in an abelian section of N(Omega) / (Omega Z), as an
# exponent vector, or fail if g does not normalise Omega; <data> has type,
# form, d, layer. Sp: the similarity factor mu mod squares. SU: det(lambda g)
# with lambda^(q0+1) mu = 1, modulo d-th powers of the scalars of GU.
# Orthogonal, layer 1 (d even): mu mod squares and det(g) / mu^(d/2) = +-1,
# with kernel SO Z. Layer 2: the spinor norm of lambda g, lambda^2 mu = 1,
# with the sign making the determinant 1 for d odd; for d even it is only
# used if -1 lies in Omega.
RECOG.ClassicalNaturalCoset := function(data,g)
  local form,f,q,mu,z,q0,lambda,c,v;
  form := data.form;
  f := form.field;
  q := Size(f);
  mu := RECOG.SimilarityFactor(g,form);
  if mu = fail then
      return fail;
  fi;
  # for SU, mu lies in GF(q0), whose elements are norms; q may be even
  if data.type = "SU" then
      z := PrimitiveRoot(f);
      q0 := form.frob;
      lambda := z^(LogFFE(mu^-1,z) / (q0+1));
      c := LogFFE((lambda^data.d * DeterminantMat(g))^-1,z^(q0-1));
      return [c mod data.order];
  fi;
  v := [0,0];
  if not RECOG.IsSquareFFE(mu,q) then
      v[1] := 1;
  fi;
  if data.type = "Sp" then
      return v{[1]};
  elif data.layer = 1 then
      if DeterminantMat(g) <> mu^(data.d/2) then
          v[2] := 1;
      fi;
      return v;
  fi;
  lambda := RootFFE(f,mu^-1,2);
  if lambda = fail then
      return fail;
  fi;
  if not IsOne(DeterminantMat(lambda * g)) then
      lambda := -lambda;
  fi;
  return [RECOG.SpinorNorm(lambda * g,form)];
end;

RECOG.HomClassicalNaturalCoset := function(data,m)
  local i,mm,v;
  i := PositionNonZeroInRow(m,1);
  mm := m;
  if not mm[1,i] in data.form.field then
      mm := mm / mm[1,i];
  fi;
  if not IsSubset(data.form.field,FieldOfMatrixList([mm])) then
      return fail;
  fi;
  v := RECOG.ClassicalNaturalCoset(data,mm);
  if v = fail then
      return fail;
  fi;
  return Product([1..Length(v)],i->data.perms[i]^v[i],());
end;

# If some generator of <ri> lies outside Omega Z, map ri onto an abelian
# section of N(Omega) / (Omega Z), see RECOG.ClassicalNaturalCoset, and
# return Success; return fail if all generators lie in Omega Z, and
# NeverApplicable if some generator does not normalise Omega. In even
# dimension PCO/POmega can be D8 (Kleidman-Liebeck, Propositions 2.7.3 and
# 2.8.2), hence two layers.
RECOG.ClassicalNaturalQuotient := function(ri,form,type)
  local d,data,imgs,H,hom;
  d := ri!.dimension;
  # for q even, CO = O Z, and O/Omega, given by the Dickson invariant, is
  # not split here: generators of O^+-(d,q) outside Omega Z fall through;
  # CSp = Sp Z, as every similarity factor is a square
  if type in ["O","Sp"] and IsEvenInt(Size(form.field)) then
      return fail;
  fi;
  data := rec( type := type, form := form, d := d, layer := 1 );
  if type = "Sp" then
      data.perms := [(1,2)];
  elif type = "SU" then
      data.order := Gcd(d,form.frob+1);
      data.perms := [CycleFromList([1..data.order])];
  elif IsEvenInt(d) then
      data.perms := [(1,2),(3,4)];
      if ForAll(GeneratorsOfGroup(Grp(ri)),
                x -> RECOG.ClassicalNaturalCoset(data,x) = [0,0]) then
          # -1 lies in SO \ Omega if its spinor norm is not trivial
          if RECOG.SpinorNorm(-One(form.gram),form) = 1 then
              return fail;
          fi;
          data.layer := 2;
          data.perms := [(1,2)];
      fi;
  else
      data.layer := 2;
      data.perms := [(1,2)];
  fi;
  imgs := List(GeneratorsOfGroup(Grp(ri)),
               x -> RECOG.HomClassicalNaturalCoset(data,x));
  if fail in imgs then
      return NeverApplicable;
  fi;
  if ForAll(imgs,IsOne) then
      return fail;
  fi;
  Info(InfoRecog,2,"ClassicalNatural: mapping onto N(",type,")/(",type,
       "Z), layer ",data.layer," image ",imgs);
  H := GroupWithGenerators(imgs);
  hom := GroupHomByFuncWithData(Grp(ri),H,RECOG.HomClassicalNaturalCoset,
                                data);
  SetHomom(ri,hom);
  Setvalidatehomominput(ri,{ri,x} -> RECOG.HomClassicalNaturalCoset(data,x)
                                     <> fail);
  Setmethodsforimage(ri,FindHomDbPerm);
  Setimmediateverification(ri,true);
  AddMethod(InitialDataForKernelRecogNode(ri).hints,
            FindHomMethodsProjective.ClassicalNatural,2000);
  return Success;
end;

# Express an element of PSp_d, PSU_d or POmega_d as an slp in terms of the
# standard generators of RECOG.ClassicalStandardGenerators.
SLPforElementFuncsProjective.ClassicalForm := function(ri,x)
  local y,lambda,pos;
  ri!.rewrite.count := ri!.rewrite.count + 1;
  if ri!.rewrite.count > 1000 then
      ri!.rewrite := RECOG.Form_RewriteSetup(ri!.classicaltype,
                                             ri!.dimension,ri!.field);
  fi;
  y := ri!.nicebas * x * ri!.nicebasi;
  y := RECOG.ScaleMatrixIntoField(y,ri!.field);
  if y = fail then
      return fail;
  fi;
  lambda := RECOG.ClassicalNaturalScalar(ri!.classicaltype,y,ri!.form);
  if lambda = fail then
      return fail;
  fi;
  y := lambda * y;
  # y and its multiples by the centre lie in the group; to make them
  # behave the same, scale by an element of the centre
  pos := PositionNonZeroInRow(y,1);
  y := RECOG.NormaliseScalarForPSLd(y[1,pos],ri!.normlist) * y;
  return RECOG.Form_Rewrite(ri!.rewrite,y);
end;

# The group with memory for RECOG.FindStdGens_* in ClassicalNatural: on
# <gens> if they are the generators of <ri> scaled (<changed>), else the
# generators of ri with memory, with the random elements of ri
RECOG.ClassicalNaturalGroupWithMemory := function(ri,gens,changed)
  local gm,pr;
  if changed then
      gm := GroupWithMemory(gens);
      pr := ProductReplacer(GeneratorsOfGroup(gm),rec(maxdepth := 500));
      gm!.pseudorandomfunc := [rec( func := Next, args := [pr] )];
  else
      # a stamp of its own, so that the first random elements are those
      # the naming test drew
      gm := Group(ri!.gensHmem);
      gm!.pseudorandomfunc := [rec(func := function(ri,name,bool)
                                      return RandomElm(ri,name,bool).el;
                                    end,
                            args := [ri,"ClassicalNaturalStdGens",true])];
  fi;
  return gm;
end;

# ClassicalNatural for <ri> containing PSp(d,q), PSU(d,q0) or
# POmega(d,q), d even for Sp, at least 4 for SU, at least 6 for Sp with
# q even and 5, 6 or at least 8 for Omega, q odd except for Sp, for SU with
# q0 <> 2 and for Omega^+-(d,q), as <classical> of RecogniseClassical
# says; <type> is "Sp", "SU" or "O", which stands for all orthogonal types
# here. The generators are scaled into Sp(d,q), SU(d,q0) or Omega(d,q).
# That needs similarity factors that are squares for Sp and Omega,
# determinants that scalars can bring to 1 for SU, and for Omega
# determinant 1 and spinor norm 1 up to the sign, resp. for q even a
# common quadratic form and Dickson invariant 0; for a conformal
# symplectic group, a unitary group with other determinants, SO(d,q) or
# O^+-(d,q), the method does not apply.
RECOG.ClassicalNaturalForm := function(ri,classical,type)
  local d,f,q,form,gens,changed,i,lambda,std,m,q0,gcd,size,eps;
  d := ri!.dimension;
  f := ri!.field;
  q := Size(f);
  if type = "Sp" then
      form := rec( gram := GramMatrix(First(classical.ClassicalForms,
                                            IsSymplecticForm)),
                   frob := 1, field := f );
  elif type = "SU" then
      q0 := RootInt(q,2);
      form := rec( gram := GramMatrix(First(classical.ClassicalForms,
                          F -> IsSesquilinearForm(F) and IsHermitianForm(F))),
                   frob := q0, field := f );
  elif IsEvenInt(q) then
      # the polar form; the quadratic form follows from the scaled
      # generators
      form := rec( gram := GramMatrix(First(classical.ClassicalForms,
                          F -> IsSesquilinearForm(F) and IsSymplecticForm(F))),
                   frob := 1, field := f );
  else
      form := rec( gram := GramMatrix(First(classical.ClassicalForms,
                          F -> IsSesquilinearForm(F) and (IsHyperbolicForm(F)
                               or IsEllipticForm(F) or IsParabolicForm(F)))),
                   frob := 1, field := f );
  fi;
  # Small cases are left to the other methods, which end in a
  # stabiliser chain
  if (q^d-1)/(q-1) <= 1000 then
      Info(InfoRecog,2,"ClassicalNatural: ",type,"(",d,",",q,") is small.");
      return TemporaryFailure;
  fi;

  i := RECOG.ClassicalNaturalQuotient(ri,form,type);
  if i <> fail then
      return i;
  fi;

  gens := ShallowCopy(GeneratorsOfGroup(Grp(ri)));
  changed := false;
  for i in [1..Length(gens)] do
      lambda := RECOG.ClassicalNaturalScalar(type,gens[i],form);
      if lambda = fail then
          Info(InfoRecog,2,"ClassicalNatural: no scalar brings a ",
               "generator into ",type,".");
          return TemporaryFailure;
      fi;
      if not IsOne(lambda) then
          gens[i] := lambda * gens[i];
          changed := true;
      fi;
  od;
  if type = "O" and IsEvenInt(q)
     and RECOG.InvariantQuadraticForm(gens,form.gram,f) = fail then
      Info(InfoRecog,2,"ClassicalNatural: the generators preserve no ",
           "common quadratic form.");
      return TemporaryFailure;
  fi;

  Info(InfoRecog,2,"ClassicalNatural: this is P",type,"_n!");
  gens := RECOG.ClassicalNaturalGroupWithMemory(ri,gens,changed);
  if type = "Sp" then
      std := RECOG.FindStdGens_Sp(gens);
  elif type = "SU" then
      std := RECOG.FindStdGens_SU(gens);
  else
      std := RECOG.FindStdGens_Omega(gens);
      type := std.type;
  fi;
  Setslptonice(ri,std.slpstd);
  ri!.nicebas := std.bas;
  ri!.nicebasi := std.basi;
  SetNiceGens(ri,List(RECOG.ClassicalStandardGenerators(type,d,f).all,
                      x->std.basi*x*std.bas));
  ri!.classicaltype := type;
  ri!.form := RECOG.ClassicalForm(type,d,f);
  ri!.rewrite := RECOG.Form_RewriteSetup(type,d,f);
  m := QuoInt(d,2);
  if type = "Sp" then
      gcd := Gcd(2,q-1);
      size := q^(m^2) * Product([1..m],i->q^(2*i)-1);
  elif type = "SU" then
      gcd := Gcd(d,q0+1);
      size := q0^(d*(d-1)/2) * Product([2..d],i->q0^i-(-1)^i);
  elif type = "O" then
      gcd := 1;
      size := q^(m^2) * Product([1..m],i->q^(2*i)-1) / 2;
  else
      # -1 lies in Omega^eps(d,q) if and only if q^m = eps mod 4 (D. E.
      # Taylor, The geometry of the classical groups, 1992, 'Order
      # Formulae, II')
      eps := 1;
      if type = "O-" then
          eps := -1;
      fi;
      gcd := 1;
      if (q^m - eps) mod 4 = 0 then
          gcd := 2;
      fi;
      size := q^(m*(m-1)) * (q^m - eps) * Product([1..m-1],i->q^(2*i)-1)
              / Gcd(2,q-1);
  fi;
  ri!.normlist := RECOG.SetupNormalisationListForPSLd(f,gcd);
  if type in RECOG.OrthogonalTypes then
      ri!.comment := Concatenation("POmega",type{[2..Length(type)]});
  else
      ri!.comment := Concatenation("P",type);
  fi;
  SetFilterObj(ri,IsLeaf);
  SetSize(ri,size / gcd);
  SetIsRecogInfoForSimpleGroup(ri,true);
  Setslpforelement(ri,SLPforElementFuncsProjective.ClassicalForm);
  return Success;
end;

#! @BeginChunk ClassicalNatural
#! TODO
#! @EndChunk
BindRecogMethod("FindHomMethodsProjective", "ClassicalNatural",
"check whether it is a classical group in its natural representation",
function(ri)
  local g,changed,classical,d,det,f,gcd,gens,gm,i,q,root,std;
  g := Grp(ri);
  d := ri!.dimension;
  f := ri!.field;
  q := Size(f);
  RECOG.SetPseudoRandomStamp(g,"ClassicalNatural");

  # First check whether we are applicable:
  classical := RecogniseClassical(g);
  # Sp(2,q) = SL(2,q) is left to the code for SL_2 below
  if d > 2 and classical.isSpContained = true and (IsOddInt(q) or d >= 6) then
      return RECOG.ClassicalNaturalForm(ri,classical,"Sp");
  elif classical.isSUContained = true and q <> 4 and d >= 4 then
      return RECOG.ClassicalNaturalForm(ri,classical,"SU");
  elif classical.isOmegaContained = true and (d = 5 or d = 6 or d >= 8)
       and (IsOddInt(q) or IsEvenInt(d)) then
      return RECOG.ClassicalNaturalForm(ri,classical,"O");
  fi;
  if classical.isSLContained <> true then
      Info(InfoRecog,2,"ClassicalNatural: Is not PSL.");
      return TemporaryFailure; # FIXME: TemporaryFailure here really correct?
  fi;

  # Now get rid of nasty determinants:
  gens := ShallowCopy(GeneratorsOfGroup(g));
  changed := false;
  gcd := Gcdex(d,q-1);
  for i in [1..Length(gens)] do
      det := DeterminantMat(gens[i]);
      if not IsOne(det) then
          root := RootFFE(f, det^-1, d);
          if root = fail then
              Info(InfoRecog,2,
                   "ClassicalNatural: determinant cannot be normalized in field.");
              return fail;
          fi;
          gens[i] := gens[i] * root;
          changed := true;
      fi;
  od;

  gm := RECOG.ClassicalNaturalGroupWithMemory(ri,gens,changed);

  if d = 2 then
      # We only have to check for (P)SL_2 since otherwise the subfield
      # method will detect it. Note that this is a projective method,
      # but a projective group contains PSL_2 if and only if the matrix
      # group generated by the same matrices (possibly scaled to make
      # the determinant to be 1) contains SL_2.

      # This is (P)SL2, lets set up the recognition:
      Info(InfoRecog,2,"ClassicalNatural: this is PSL_2!");
      std := RECOG.RecogniseSL2Natural(gm,f);
      ri!.comment := "PSL2";
      Setslptonice(ri,SLPOfElms(std.all));
      ri!.nicebas := std.bas;
      ri!.nicebasi := std.basi;
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
          if (q^d-1)/(q-1) <= 1000 then
              Info(InfoRecog,2,"Classical natural: SL(",d,",",q,"): small ",
                   "case, handing over to Schreier-Sims.");
              ri!.comment := Concatenation("SL(",String(d),",",String(q),")",
                                           "_StabilizerChain");
              return FindHomMethodsProjective.StabilizerChainProj(ri);
          fi;
          Info(InfoRecog,2,"ClassicalNatural: this is PSL_n!");
          std := RECOG.FindStdGens_SL(gm);
          Setslptonice(ri,std.slpstd);
          ri!.nicebas := std.bas;
          ri!.nicebasi := std.basi;
          SetNiceGens(ri,List(RECOG.ClassicalStandardGenerators("SL",d,f).all,
                      x->std.basi*x*std.bas));
          ri!.rewrite := RECOG.SL_RewriteSetup(d,f);
          ri!.comment := "PSLd";
          ri!.gcd := gcd;
          SetFilterObj(ri,IsLeaf);
          SetSize(ri,Product([0..d-1],i->(q^d-q^i))/((q-1)*gcd.gcd));
          SetIsRecogInfoForSimpleGroup(ri,true);
          Setslpforelement(ri,SLPforElementFuncsProjective.PSLd);
          return Success;
      fi;
  fi;

  return TemporaryFailure; # FIXME: TemporaryFailure here really correct?

end);
