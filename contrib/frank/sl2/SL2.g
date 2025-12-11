##### (c)  Frank Lübeck ############


#Read("slptools.gd");
#Read("memory.gd");
#Read("slptools.gi");
#Read("memory.gi");

###########################################################################
#########  generalities for iterators   ----  move in GAP library
#   throw away   "TrivialIterator" and companions! (unfortunately
#   documented, only used once in  modulrow.gi)

# Generic iterator <iter> from a record. This record should have components:
#   .next(<iter>)     a function called by NextIterator(<iter>)
#   .done             which should always be set to answer of IsDoneIterator

BindGlobal("IteratorTypeGeneric",
           NewType(IteratorsFamily, IsMutable and IsIterator));
InstallOtherMethod(Iterator, [IsRecord], function( r )
  return Objectify(IteratorTypeGeneric, r);
end);
InstallOtherMethod(IsDoneIterator, [IsIterator], function( it )
  return it!.done;
end);
InstallOtherMethod(NextIterator, [IsIterator], function( it )
  return it!.next(it);
end);
###########################################################################


# an Info class 
InfoGrpRec := NewInfoClass("InfoGrpRec");
SetInfoLevel(InfoGrpRec, 3);

# minimal m with (a/b)^m <= r/s
MinPowerRat := function(a, b, r, s)
  local m, aa, bb;
  m := 1;
  aa := s*a;
  bb := r*b;
  while aa > bb do
    m := m+1;
    aa := aa*a;
    bb := bb*b;
  od;
  return m;
end;


####   not good, because "Order" can be very bad
FindElementsOrders := function(arg)
  local grp, orders, max, res, g, ord, pos, i, found;
  grp := arg[1];
  orders := arg[2];
  if Length(arg) > 2 then
    max := arg[3];
  else
    max := 100;
  fi;
  res := [];
  found := 0;
  for i in [1..max] do
    g := PseudoRandom(grp);
    ord := Order(g);
    pos := Position(orders, ord);
    if pos <> fail and not IsBound(res[pos]) then
      res[pos] := g;
      found := found+1;
      if found = Length(orders) then
        return res;
      fi;
    fi;
  od;
  Info(InfoGrpRec, 3, "Found elements of orders ",
      orders{Filtered([1..Length(orders)], i-> IsBound(res[i]))},
      "(of ",orders,") in ",i," sample elements");
  return res;
end;
 
ElementOfOrder := function(G, ord, max)
  local ps, one, x, i;
  ps := Set(FactorsInt(ord));
  if ps[1] = ord then
    ps := [];
  fi;
  one := One(G);
  if ord = 1 then
    return one;
  fi;
  for i in [1..max] do
    x := PseudoRandom(G);
    if x <> one and x^ord = one and ForAll(ps, p-> x^(ord/p) <> one) then
      Info(InfoGrpRec, 3, "Found element of order ",ord," in ",i," samples.");
      return x;
    fi;
  od;
  Info(InfoGrpRec, 3, "No element of order ",ord," in ",i," samples.");
  return fail;
end;



# Here basis must be an F_p basis of U and not empty, p is the characteristic.
# Calls to NextIterator yield pairs [u, coeffs] where u is an element of U
# and coeffs are the coordinates of u with respect to basis.
# It is guaranteed that the identity element of U comes first.
IteratorUByFpBasis := function(basis, p)
  local e, r;
  e := Length(basis);
  r := rec(
    basis := basis,
    p := p,
    q := p^e,
    oneFp := One(GF(p)),
    coeffs := Concatenation([-1], 0*[2..e]),
    u := basis[1]^-1,
    count := 0,
    done := false,
    IsDoneIterator := function(it)
      return it!.done;
    end,
    ShallowCopy := fail,
    NextIterator := function(it)
      local b, c, p, i;
      b := it!.basis;
      c := it!.coeffs;
      p := it!.p;
      i := 1;
      c[i] := c[i] + 1;
      it!.u := it!.u * b[i];
      while c[i] = p do
        c[i] := 0;
        i := i+1;
        c[i] := c[i] + 1;
        it!.u := it!.u * b[i];
      od;
      it!.count := it!.count + 1;
      if it!.count = it!.q then
        it!.done := true;
      fi;
      return [it!.u, it!.coeffs * it!.oneFp];
    end);
  return IteratorByFunctions(r);
end;

# iterator for tuples (a1,...,an), ai in Si
# arg is list of Si
IteratorTuples := function(arg)
  local r;
  r := rec(
    lists := arg,
    n := Length(arg),
    max := List(arg, Length),
    # zero based current positions
    poss := 0*[1..Length(arg)],
    count := 0,
    IsDoneIterator := function(it)
      return it!.count >= Product(List(arg, Length));
    end,
    ShallowCopy := fail,
    NextIterator := function(it)
      local i;
      i := 1;
      it!.poss[i] := it!.poss[i]+1;
      while it!.poss[i] = it!.max[i] do
        it!.poss[i] := 0;
        i := i+1;
        it!.poss[i] := it!.poss[i]+1;
      od;
      it!.count := it!.count+1;
      return List([1..it!.n], i-> it!.lists[i][it!.poss[i]+1]);
    end);
  r!.poss[1] := -1;
  return IteratorByFunctions(r);
end;

# we choose generating set [t, u, us] with t = h(zeta), u = u_alpha(1),
# us = u_-alpha(1)
RecognizingGeneratorsSL2 := function(q)
  local one, t, u, us, z;
  one := One(SL(2,q));
  z := PrimitiveRoot(GF(q));
  t := List(one, ShallowCopy);
  t[1][1] := z^-1;
  t[2][2] := z;
  u := List(one, ShallowCopy);
  u[2][1] := z^0;
  us := List(one, ShallowCopy);
  us[1][2] := z^0;
  List([t,u,us], a-> ConvertToMatrixRep(a, q));
  return [t, u, us];
end;


# straight line program for [t, u, us, x_alpha(c)] from [t, u, us]
SLPthetasquare := function(c, p, e)
  local n, ucslp, Fq, theta, bas, ai, lines, l, i;
  if e = 1 then
    if p < 65536 then
      n := IntFFE(c);
    else
      n := c![1];
    fi;
    ucslp := StraightLineProgram([[[1,1], [2,1], [3,1], 
                                      [2, n]]], 3);
  else
    Fq := GF(p,e);
    theta := PrimitiveRoot(Fq);
    # Express theta as linear combination of 1, theta^2, theta^(2(f-1)).
    bas := Basis(Fq, List([0..e-1], i-> theta^(2*i)));
    ai := IntVecFFE(Coefficients(bas, c));
    lines := [[2, 1]];
    for i in [1..e-1] do
      Add(lines, [1, 1, 3+i, 1, 1, -1]);
    od;
    l := [];
    for i in [1..e] do
      if ai[i] <> 0 then
        Append(l, [i+3, ai[i]]);
      fi;
    od;
    Add(lines, [[1,1],[2,1],[3,1],l]);
    ucslp := StraightLineProgram(lines, 3);
  fi;
  return ucslp;
end;

InstallMethod(IntFFE, [IS_FFE and IsZmodnZObj], function(a)
  return a![1];
end);

# small utility, to be adjusted when new fields become available
DeclareOperation("IntCoeffsModPrimitivePolynomial", 
   [IsField and IsFinite, IsRingElement]);

InstallMethod(IntCoeffsModPrimitivePolynomial, 
  [IsFinite and IsField, IsRingElement],
function(F, x)
  local pol, z, res;
  if IsZero(x) then
    return [];
  fi;
  if Size(F) <= 65536 then
    pol := DefiningPolynomial(F);
    z := IndeterminateOfLaurentPolynomial(pol);
    res := PowerMod(z, LogFFE(x, PrimitiveRoot(F)), pol);
    return IntVecFFE(CoefficientsOfUnivariatePolynomial(res));
  else
    # currently only prime fields
    return [x![1]];
  fi;
end);


# x in standard SL(2,p^e) expressed as straight line program with respect to
# RecognizingGeneratorsSL2(p^e)
SLPinStandardSL2 := function(x, p, e)
  local F, z, z2, bas, lk, mfr, t, u, us, n, tinv, ualphazeta2, 
        uaz, ualphazeta, a, b, c, d, l, mx, i, one;
  F := GF(p,e);
  z := PrimitiveRoot(F);
  # cache for prim. gen. z the linear comb. of z in [1, z^2, z^4, ..., z^(e-1)]
  if not IsBound(F!.primrtlksq) then
    z2 := z^2;
    bas := [z^0];
    for i in [1..e-1] do
      Add(bas, bas[i] * z2);
    od;
    bas := Basis(F, bas);
    lk := IntVecFFE(Coefficients(bas, z));
    F!.primrtlksq := lk;
  else
    lk := F!.primrtlksq;
  fi;
  # Here the group is not important, only the memory is used for efficient
  # bookkeeping of straight line programs.
  mfr := GroupWithMemory(Group([(),(),()]));
  t := mfr.1; u := mfr.2; us := mfr.3;
  n := u * us^-1 * u;
  tinv := t^-1;
  # create a list [u_alpha(zeta^i)| i=0..e-1]
  if e > 1 then
    ualphazeta2 := [u];
    for i in [1..e-1] do
      Add(ualphazeta2, t*ualphazeta2[i]*tinv);
    od;
    uaz := Product([1..Length(lk)], i-> ualphazeta2[i]^lk[i]);
    ualphazeta := [u, uaz];
    while Length(ualphazeta) < e do
      Append(ualphazeta, [t*ualphazeta[Length(ualphazeta)-1]*tinv,
                          t*ualphazeta[Length(ualphazeta)]*tinv]);
    od;
  else
    ualphazeta := [u];
  fi;
  # now consider x
  a := x[1][1]; b := x[1][2]; c := x[2][1]; d := x[2][2];
  if IsZero(b) then
    # make sure b <> 0 by mult. with us^-1
    b := b-a; d := d-c;
  fi;
  one := One(mfr);
  l := IntCoeffsModPrimitivePolynomial(F, (d-1)/b);
  mx := Product([1..Length(l)], i-> ualphazeta[i]^l[i], one);
  l := IntCoeffsModPrimitivePolynomial(F, -b);
  mx := mx * Product([1..Length(l)], i-> ualphazeta[i]^l[i], one)^n;
  l := IntCoeffsModPrimitivePolynomial(F, (a-1)/b);
  mx := mx * Product([1..Length(l)], i-> ualphazeta[i]^l[i], one);
  if IsZero(x[1][2]) then
    mx := mx * us;
  fi;

  return SLPOfElm(mx);
end;

# straight line program in black box SL(2,p^e) for element g and given
# images stdgens of [t,u,us]
MatrixElementBlackBoxSL2 := function(g, p, e, stdgens)
  local F, z, t, u, us, n, tinv, bas, inB, tuus, nmat, 
        gg, res, it, l, uu, a, v, i;
  F := GF(p,e);
  z := PrimitiveRoot(F);
  t := stdgens[1]; u := stdgens[2]; us := stdgens[3];
  n := u * us^-1 * u;
  tinv := t^-1;
  bas := [u];
  for i in [1..e-1] do
    Add(bas, t*bas[i]*tinv);
  od;
  
  # find a, b in F for g1 = h_alpha(a) u_alpha(b) in B
  inB := function(g1)
    local it, v, l, a, h, b, i, mat;
    it := IteratorUByFpBasis(bas, p);
    v := u^g1;
    l := NextIterator(it);
    while not IsDoneIterator(it) and v <> l[1] do
      l := NextIterator(it);
    od;
    if v <> l[1] then
      return fail;
    fi;
    # decide correct root a and divide by h_alpha(a)
    a := SquareRoots(F, List([1..Length(l[2])], i-> z^(2*i-2)) * l[2]);
    h := [[a[1]^-1, 0], [0, a[1]]]*z^0;
    ConvertToMatrixRep(h, p^e);
    h := SLPinStandardSL2(h, p, e);
    h := ResultOfStraightLineProgram(h, stdgens);
    if not IsOne((h * g1)^p) then
      a :=  a[2];
      h := h * t^((p^e-1)/2);
    else
      a := a[1];
    fi;
    v := h * g1;
    it := IteratorUByFpBasis(bas, p);
    l := NextIterator(it);
    while not IsDoneIterator(it) and v <> l[1] do
      l := NextIterator(it);
    od;
    if v <> l[1] then
      return fail;
    fi;
    b := List([1..Length(l[2])], i-> z^(2*i-2)) * l[2];
    #return [a, b];
    mat := [[a, 0*a], [a^-1*b, a^-1]];
    ConvertToMatrixRep(mat, p^e);
    return mat;
  end;
  
  tuus := RecognizingGeneratorsSL2(p^e);
  nmat := tuus[2]*tuus[3]^-1*tuus[2];
  gg := us^g;
  if gg*u = u*gg then
    # rare case n*g is in B
    res := inB(n*g);
    if res = fail then
      return fail;
    fi;
    res := nmat^-1 *res;
    return res;
  fi;
  # now n*g is not in B, so gg is not in B and can be conj. back into
  # B^- by unique elt. u(a) in U
  it := IteratorUByFpBasis(bas, p);
  l := NextIterator(it); 
  uu := us^l[1];
  while not IsDoneIterator(it) and uu*gg <> gg*uu do
    l := NextIterator(it);
    uu := us^l[1];
  od;
  if uu*gg <> gg*uu then
    return fail;
  fi;
  res := inB((g*l[1]^-1)^n);
  if res = fail then
    return fail;
  fi;
  a := List([1..Length(l[2])], i-> z^(2*i-2)) * l[2];
  v := [[z^0, 0*z], [a, z^0]];
  ConvertToMatrixRep(v, p^e);
  return nmat * res * nmat^-1 *
  v;
end;

    


# pr, pr_1, pr_2, ..., pr_k
# where pr_i get same list of generators and have one element results, and
# where pr gets results of pr_1, ..., pr_k as input
# the resulting slp gets same input as pr_1, ... pr_k and returns result of pr
CombinedStraightLineProgram := function(arg)
  local n, lines, pos, pri, d, ll, pr, k, l, i;
  n := NrInputsOfStraightLineProgram(arg[2]);
  lines := [];
  pos := [];
  for i in [2..Length(arg)] do
    pri := LinesOfStraightLineProgram(arg[i]);
    d := Length(lines);
    for l in pri do
      ll := [];
      for i in [1..Length(l)/2] do
        if l[2*i-1] <= n then
          Add(ll, l[2*i-1]);
        else
          Add(ll, l[2*i-1]+d);
        fi;
        Add(ll, l[2*i]);
      od;
      Add(lines, ll);
    od;
    Add(pos, Length(lines));
  od;
  pr := LinesOfStraightLineProgram(arg[1]);
  d := Length(lines);
  k := Length(arg)-1;
  for i in [1..Length(pr)] do
    l := pr[i];
    ll := [];
    for i in [1..Length(l)/2] do
      if l[2*i-1] <= k then
        Add(ll, pos[l[2*i-1]]+n);
      else
        Add(ll, l[2*i-1]-k+d+n);
      fi;
      Add(ll, l[2*i]);
    od;
    Add(lines, ll);
  od;
  return StraightLineProgram(lines, n);
end;
    
# u, us and t are elements of some group, let G = <u, us, t>. This function
# checks if
#     SL(2,q)   ->   G,  [[1,0],[1,1]] -> u,   [[1,1],[0,1]] -> us,
#                        [[theta^-1,0],[0,theta]] -> t
# defines a homomorphism.

# first special case q = 2^f 
CheckSL2RelationsChar2 := function(t, u, us, f, theta)
  local one, q, x, y, z, a, Fq, bas, ai, i, h;
  
  # 1 in group G
  one := t^0;
  q := 2^f;
  
  # Relations not correct for q = 2, but then group is not simple, 
  # we use brute force.
  if q = 2 then
    h := GroupHomomorphismByImages(SL(2,2), Group(t, u, us), 
         Z(2)^0*[[[1,0],[0,1]], [[1,0],[1,1]], [[1,1],[0,1]]],
         [t, u, us]);
    if h = fail then
      Info(InfoGrpRec, 3, "Brute force check for SL(2,2) failed.");
      return false;
    else
      return true;
    fi;
  fi;
  
  # Transform generators to Sinkov generators x, y, z and check Sinkov 
  # relations. 
  x := t*us;
  # x^(q-1) = 1
  if x^(q-1) <> one then
    Info(InfoGrpRec, 3, "SL2(2^f) relation x^(q-1) = 1 fails.");
    return false;
  fi;
  y := us;
  z :=  u*us;
  # y^2 = 1 and z^3 = 1
  if y^2 <> one or z^3 <> one then
    Info(InfoGrpRec, 3, "SL2(2^f) relation y^2 = 1 and z^3 = 1 fails.");
    return false;
  fi;
  # (x z)^2 = 1 and (y z)^2 = 1
  if (x*z)^2 <> one or (y*z)^2 <> one then
    Info(InfoGrpRec, 3, "SL2(2^f) relation (x z)^2 = 1 and (y z)^2 = 1 fails.");
    return false;
  fi;
  # (x^i y x^-i y^-1)^2 = 1, i = 1,.., f-1   (note y^-1 = y)
  a := y;
  for i in [1..f-1] do
    a := x*a/x;
    if (a*y)^2 <> one then
      Info(InfoGrpRec, 3, "SL2(2^f) relation (x^i y x^-i y^-1)^2 = 1 fails.");
      return false;
    fi;
  od;
  
  if f = 1 then
    # x = y x y^1
    if x <> y*x*y then
      Info(InfoGrpRec, 3, "SL2(2^f) relation x = y x y^1 fails.");
      return false;
    else
      return true;
    fi;
  else
    Fq := GF(q);
    bas := Basis(Fq, List([0..f-1], i-> theta^i));
    ai := IntVecFFE(Coefficients(bas, theta^f));
    # x^f = y (x y^{a_{f-1}}) ... (x y^{a_0}), where 
    # theta^f = sum_{i=0}^{f-1} a_i theta^i
    if x^f <> y * Product([f-1, f-2..0], i-> x*y^ai[i+1]) then
      Info(InfoGrpRec, 3, "SL2(2^f) relation x^f = y (x y^{a_{f-1}}) ... (x y^{a_0}) failed.");
      return false;
    else
      return true;
    fi;
  fi;
end;
    
CheckSL2Relations := function(t, u, us, q, theta)
  local f, p, Fq, one, U, R, S0, S1, bas, ai, S, ci, di, i, h;
  # Relations not correct for q = 3, but then group is not simple, 
  # we use brute force.
  if q = 3 then
    h := GroupHomomorphismByImages(SL(2,3), Group(t, u, us), 
         Z(3)^0*[[[-1,0],[0,-1]], [[1,0],[1,1]], [[1,1],[0,1]]],
         [t, u, us]);
    if h = fail then
      Info(InfoGrpRec, 3, "Brute force check for SL(2,3) failed.");
      return false;
    else
      return true;
    fi;
  fi;
  f := FactorsInt(q);
  p := f[1];
  f := Length(f);
  # Characteristic 2 is an extra case.
  if p = 2 then
    return CheckSL2RelationsChar2(t, u, us, f, theta);
  fi;
  Fq := GF(q);
  # one in G
  one := u^0;
  
  # Use Todd-relations, transform to images of Todd generators and check
  # relations when ingredients available.
  U := u*us^-1;
  # U^6 = 1
  if U^6 <> one then
    Info(InfoGrpRec, 3, "SL2 relation U^6 = 1 fails.");
    return false;
  fi;
  R := u*t;
  # R^(q-1) = 1 and (U R)^4 = 1
  if R^(q-1) <> one or (U*R)^4 <> one then
    Info(InfoGrpRec, 3, "SL2 relation R^(q-1) = 1 and (U R)^4 = 1 fails.");
    Error();
    return false;
  fi;
  S0 := u;
  # S0^p = 1 and (U S0)^4 = 1
  if S0^p <> one or (U*S0)^4 <> one then
    Info(InfoGrpRec, 3, "SL2 relation S0^p = 1 and (U S0)^4 = 1 fails.");
    return false;
  fi;
  # S1 should become image of [[1,0],[theta,1]], by conjugation with t
  # we get the [[1,0],[theta^(2i),1]].
  if f = 1 then
    if p > 65536 then
      S1 := S0^theta![1];
    else
      S1 := S0^IntFFE(theta);
    fi;
  else
    # Express theta as linear combination of 1, theta^2, theta^(2(f-1)).
    bas := Basis(Fq, List([0..f-1], i-> theta^(2*i)));
    ai := IntVecFFE(Coefficients(bas, theta));
    S1 := Product([0..f-1], i-> (S0^(t^-i))^ai[i+1]);
  fi;
  # S1^p = 1 and S0 S1 = S1 S0 and (S1 R U)^6 = 1
  if S1^p <> one or S0*S1 <> S1*S0 or (S1*R*U)^6 <> one then
    Info(InfoGrpRec, 3, "SL2 relation S1^p = 1 and S0 S1 = S1 S0 and (S1 R U)^6 = 1 fails.");
    return false;
  fi;
  
  S := [S0, S1];
  # fill by conjugating with R^-1, yields R S[i] = S[i+2] R
  for i in [2..f-1] do
    Add(S, R*S[i-1]*R^-1);
    # S[i] S[j] = S[j] S[i]
    if ForAny([1..i], j-> S[j]*S[i+1] <> S[i+1]*S[j]) then
      Info(InfoGrpRec, 3, "SL2 relation S[i] S[j] = S[j] S[i] fails.");
      return false;
    fi;
  od;
  # Relations S[i]^p = 1 follow, since correct for i=0,1.
  
  # It remains to check the field arithmetic relations.
  # Express theta^f = sum_{i=0}^{f-1} c_i theta^i and 
  # theta^{f+1} = sum_{i=0}^{f-1} d_i theta^i and check
  # R S_{f-2} R^-1 = prod_{i=0}^{f-1} S_i^c_i   (for f > 1) and
  # R S_{f-1} R^-1 = prod_{i=0}^{f-1} S_i^d_i 
  if f = 1 then
    if p > 65536 then
      ci := theta![1];
    else
      ci := IntFFE(theta);
    fi;
    if R*S0*R^-1 <> S0^(ci^2 mod p) then
      Info(InfoGrpRec, 3, "SL2 relation R*S0*R^-1 <> S0^(ci^2 mod p) fails.");
      return false;
    fi;
  else
    bas := Basis(Fq, List([0..f-1], i-> theta^(i)));
    ci := IntVecFFE(Coefficients(bas, theta^f));
    if R * S[f-1] * R^-1 <> Product([0..f-1], i-> S[i+1]^ci[i+1]) then
      Info(InfoGrpRec, 3, "SL2 relation R S_{f-2} R^-1 = prod_{i=0}^{f-1} S_i^c_i fails.");
      return false;
    fi;
    di := [ci[f]*ci[1]];
    for i in [1..f-1] do
      Add(di, ci[f]*ci[i+1] + ci[i]);
    od;
    if R * S[f] * R^-1 <> Product([0..f-1], i-> S[i+1]^di[i+1]) then
      Info(InfoGrpRec, 3, "SL2 relation R S_{f-1} R^-1 = prod_{i=0}^{f-1} S_i^d_i  fails.");
      return false;
    fi;
  fi;
  return true;
end;


# this produces a surjective homomorphism from standard SL(2,q) to G 
# (isomorphic to SL(2,q) or PSL(2,q))
# if u is given it must be a nontrivial unipotent element 
# args:  G, q[, u]
HomMatBlackSL2 := function(arg)
  local G, one, q, Fq, p, e, theta, s, t, u, o, i, us, tt, ut, basis, U, Us, 
        b, x, mipol, oldt, stdgens, f, pre, pregen, sl, hom;
  G := arg[1];
  one := One(G);
  q := arg[2];
  Fq := GF(q);
  p := Factors(q);
  e := Length(p);
  p := p[1];
  # standard generator of Fq^*
  theta := PrimitiveRoot(Fq);

  # search for q-1 and q+1 element and if we don't find it, we assume
  # to have a PSL_2(q) and search for (q-1)/2 and (q+1)/2 elements.
  s := ElementOfOrder(G, q+1, 50);
  if s = fail then
    # no element of order q+1 means we are in PSL_2(q)
    t := ElementOfOrder(G, (q-1)/2, 50);
    if t = fail then
      return fail;
    fi;
    s := ElementOfOrder(G, (q+1)/2, 50);
    if s = fail then
      return fail;
    fi;
  else
    # catch case q=3 with only one 2-element
    if q = 3 then 
      t := s^2;
    else
      t := ElementOfOrder(G, q-1, 50);
    fi;
    if t = fail then
      return fail;
    fi;
  fi;
                  
  # search for p-element (if not given as argument)
  if Length(arg) > 2 then
    u := arg[3];
  else
    o := GcdInt(p-1, 2) * p;
    i := 1; 
    while i < 5*q do
      u := PseudoRandom(G);
      if u^o = one and u^(o/p) <> one then
        u := u^(o/p);
        break;
      else
        u := fail;
      fi;
      i := i+1;
    od;
    if u = fail then
      return fail;
    else
      Info(InfoGrpRec, 3, "#I  Found element of order p in ",i," samples.\n");
    fi;
  fi;
  # second p-element may also be given
  if Length(arg) > 3 then
    us := arg[4];
  else
    repeat
      us := u^PseudoRandom(G);
    until us * u <> u * us;
  fi;
  
  # search for conjugate of t normalizing root subgroup of u
  tt := t;
  ut := u^t;
  while ut*u <> u*ut do
    t := t^s;
    ut := u^t;
    if tt = t then
      t := t^PseudoRandom(G);
      ut := u^t;
      tt := t;
    fi;
  od;
  # now find conjugate of t in B which also normalizes root subgroup of us
  # (search all U-conjugates of t)
  basis := [u];
  for i in [1..e-1] do
    Add(basis, basis[i]^t);
  od;
  U := IteratorUByFpBasis(basis, p);
  tt := t;
  for x in U do
    t := tt^x[1];
    ut := us^t;
    if ut*us = us*ut then
      break;
    fi;
  od;

  # now we need to traverse the root subgroup of us to find the image of
  # u_-alpha(-1), afterwards we redefine us as image of u_-alpha(1).
  
  # (to simplify element order check, we throw out 1 in Us, which comes
  # first)
  
  # a basis of the root subgroup of us as vectorspace over F_p
  basis := [us];
  for i in [1..e-1] do
    Add(basis, basis[i]^t);
  od;

  Us := IteratorUByFpBasis(basis, p);
  NextIterator(Us);
  if p = 2 then
    for x in Us do
      if (u*x[1])^3 = one then
        us := x[1];
        break;
      fi;
    od;
  else
    for x in Us do
      if (u*x[1]*u)^4 = one then
        us := x[1]^-1;
        break;
      fi;
    od;
  fi;
  
  # Next we want to substitute t by some primitive power which acts on Us
  # like h_alpha(Z(q)). If t acts like h_alpha(eps) we compute now the
  # minimal polynomial of eps^2 on Us as F_p vector space.
  b := basis[e]^t;
  for x in IteratorUByFpBasis(basis, p) do
    if x[1] = b then
      break;
    fi;
  od;
  x := -x[2];
  Add(x, One(Fq));
  mipol := UnivariatePolynomial(Fq, x);
  # we get eps^2
  x := RootsOfUPol(Fq, mipol)[1];
  # now eps or -eps
  x := SquareRoots(Fq, x)[1];
  # if p=2 or q = 3 mod 4, it is easy to find the right root
  # In case q = 1 mod 4 we cannot find the correct x here, so maybe we have
  # to switch x to -x below if the relations are not fulfilled.
  if p<>2 and x^((q-1)/2) = One(Fq) then
    x := -x;
  fi;
  
  # redefine t
  oldt := t;
  if q <= 65536 then
    t := oldt^LogFFE(theta, x);
  else
    t := oldt^LogMod(theta![1], x![1], p);
  fi;
  
  if CheckSL2Relations(t, u, us, q, theta) then
    stdgens := [t, u, us];
  elif q mod 4 = 1 then
    # try with -x
    x := -x;
    if q <= 65536 then
      t := oldt^LogFFE(theta, x);
    else
      t := oldt^LogMod(theta![1], x![1], p);
    fi;
    if CheckSL2Relations(t, u, us, q, theta) then
      stdgens := [t, u, us];
    else
      return fail;
    fi;
  else
    return fail;
  fi;

  # construct the homomorphism (by functions) and check surjectivity
  f := x-> ResultOfStraightLineProgram(SLPinStandardSL2(x, p, e), stdgens);
  pre := x-> MatrixElementBlackBoxSL2(x, p, e, stdgens);
 
  Info(InfoGrpRec, 3, "Searching preimages of given generators . . .");
  pregen := [];
  for x in GeneratorsOfGroup(G) do
    Add(pregen, pre(x));
    if pregen[Length(pregen)] = fail then
      Info(InfoGrpRec, 3, "Constructed map is not surjective!");
      return fail;
    fi;
  od;
  Info(InfoGrpRec, 3, "Ok, constructed map is surjective.");
  sl := SL(2, q);
  if p = 2 or f(-One(sl)) <> One(G) then
    hom := GroupHomomorphismByFunction(sl, G, f, pre);
  else
    hom := GroupHomomorphismByFunction(sl, G, f, false, pre);
  fi;
  return hom;  
end;



  

SL2Test := function(arg)
  local g, q, num, times, t, a, i;
  g := arg[1]; q := arg[2]; num := arg[3];
  times := [];
  for i in [1..num] do
    t := Runtime();
    if Length(arg)=4 then
      a := HomMatBlackSL2(g, q, arg[4]);
    else
      a := HomMatBlackSL2(g, q);
    fi;
    Add(times, Runtime()-t);
    Print("*\c");
  od;
  return times;
  
end;

SL2Test2 := function()
  local i, g, t, h, u, p, j;
  SetInfoLevel(InfoGrpRec, 0);
  for p in Primes do
    i := 1;
    while p^i < 1000 do
      g := SL(2,p^i);
      Print("Testing ",p,"^",i, ":  \c");
      t := Runtime();
      for j in [1..10] do 
        h := HomMatBlackSL2(g, p^i);
        if h = fail then Print("*\c"); fi;
      od;
      Print(" Time w/o p-elt: ", Runtime()-t, "   \c");
      u := ElementOfOrder(g, p, 10*p^i);
      t := Runtime();
      for j in [1..10] do 
        h := HomMatBlackSL2(g, p^i, u);
        if h = fail then Print("*\c"); fi;
      od;
      Print("Time with p-elt: ",Runtime()-t, "\n");
      i := i+1;
    od;
  od;
  SetInfoLevel(InfoGrpRec, 3);
end; 
    
  
  
