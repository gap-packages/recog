#####   Frank Lübeck ############



Read("SL2.g");

# a utility to produce  generators of SL3's
GenericGeneratorsSL3 := function()
  local id, a, b, c, as, bs, cs, h;
  id := IdentityMat(3);
  a := List(id, ShallowCopy);
  a[2][1] := Indeterminate(Rationals, "a");
  b := List(id, ShallowCopy);
  b[3][2] := Indeterminate(Rationals, "b");
  c := List(id, ShallowCopy);
  c[3][1] := Indeterminate(Rationals, "c");
  as := List(id, ShallowCopy);
  as[1][2] := Indeterminate(Rationals, "as");
  bs := List(id, ShallowCopy);
  bs[2][3] := Indeterminate(Rationals, "bs");
  cs := List(id, ShallowCopy);
  cs[1][3] := Indeterminate(Rationals, "cs");
  h := DiagonalMat([Indeterminate(Rationals, "l1"),
                    Indeterminate(Rationals, "l2"),
                    Indeterminate(Rationals, "l3")]);
  return [a,as,b,bs,c,cs,h]*Indeterminate(Rationals)^0;
end;

# should be in GAP library
InstallOtherMethod(Value, [IsList, IsObject], 
function(l, a)
  return List(l, x-> Value(x, a));
end);

# our set of generators for standard SL3(q)
RecognizingGeneratorsSL3 := function(q)
  local fac, p, e, F, z, gen, h, fqbas;
  fac := FactorsInt(q);
  p := fac[1];
  e := Length(fac);
  F := GF(p,e);
  z := PrimitiveRoot(F);
  gen := GenericGeneratorsSL3();
  h := gen[7];
  fqbas := List([0..e-1], i-> z^i);
  return Concatenation(List([1..6], i-> List(fqbas, a-> Value(gen[i], a))));
end;

# for testing, using random commutators doesn't seem to work well with
# small groups
TryDerivedGroup := function(arg)
  local G, n, l;
  G := arg[1];
  if Length(arg) > 1 then
    n := arg[2];
  else
    n := 3;
  fi;
  l := List([1..n], i-> PseudoRandom(G));
  return SubgroupNC(G, [Comm(l[1], l[2]), Comm(l[2], l[3])]);
end;

# This is the special case we need below.
# Use Dickson's theorem: if q <> 2,3,5,7 then SL_2(q) has no proper subgroup
# containing an element of order q-1 and an element of order q+1.
DerivedGL2 := function(G, q)
  local gen, res, one, ps, x1, y, x2;
  if q = 2 then return G; fi;
  gen := [PseudoRandom(G), PseudoRandom(G)];
  res := [Comm(gen[1], gen[2])];
  if q in [3, 5, 7] then
    while Size(Group(res)) < Size(SL(2,q)) do
      y := PseudoRandom(G);
      Append(res, List(gen, a-> Comm(a, y)));
    od;
    return SubgroupNC(G, res);
  fi;
  one := One(G);
  x1 := ElementOfOrder(Group(res), q+1, 20);
  while x1 = fail do
    y := PseudoRandom(G);
    Append(res, List(gen, a-> Comm(a, y)));
    Add(gen, y);
    x1 := ElementOfOrder(Group(res), q+1, 20);
  od;
  x2 := ElementOfOrder(Group(res), q-1, 20);
  while x2 = fail do
    y := PseudoRandom(G);
    Append(res, List(gen, a-> Comm(a, y)));
    Add(gen, y);
    x2 := ElementOfOrder(Group(res), q-1, 20);
  od;
  return SubgroupNC(G, [x1, x2]);
end;
  
    

HomMatBlackSL3 := function(arg)
  local G, one, q, Fq, p, e, x, s, t, gg, galpha, u, hh, gbeta, genSL2, K, hK, ua, uma, T, tmp, bK, pre, M, hM, bM, genimg, psi, negC, z, bas, mpos, mneg, k, m, a, i, j, ii, jj;
  G := arg[1];
  one := One(G);
  q := arg[2];
  Fq := GF(q);
  p := Factors(q);
  e := Length(p);
  p := p[1];

  # First find a set of root subgroups
  #   random (q^2-1)-element, take (q+1)-st power s
  x := ElementOfOrder(G, q^2-1, 100);
  if x = fail then
    return fail;
  fi;
  s := x^(q+1);
  #   find conjugate t of s such that <s,t> is a GL2, find (q^2-1)-elt in
  #   there, galpha is its (q+1)-st power
  for i in [1..20] do
    t := s^PseudoRandom(G);
    gg := SubgroupNC(G, [s, t]);
    x := ElementOfOrder(gg, q^2-1, 30);
    if x <> fail then
      galpha := x^(q+1);
      break;
    else
      gg := 0;
    fi;
  od;
  if gg=0 then
    return fail;
  fi;
  #   Find conjugate u of s such that <galpha,u> is a GL2, find (q^2-1)-elt in
  #   there.
  for i in [1..20] do
    u := s^PseudoRandom(G);
    hh := SubgroupNC(G, [galpha, u]);
    x := ElementOfOrder(hh, q^2-1, 30);
    if x <> fail then
      gbeta := x^(q+1);
      break;
    else
      gg := 0;
    fi;
  od;
  if gg=0 then
    return fail;
  fi;
  #   Use SL2 recognition for K = <s,t>'
  genSL2 := RecognizingGeneratorsSL2(q);
  K := DerivedGL2(gg, q);
  hK := HomMatBlackSL2(K, q);
  # find 2x2-matrix acting on standard SL2 like gbeta on K
  ua := Image(hK, genSL2[2]);
  ua := PreImageElm(hK, ua^gbeta);
  uma := Image(hK, genSL2[3]);
  uma := PreImageElm(hK, uma^gbeta);
  T := [NullspaceMat(ua-ua^0)[1]];
  Add(T, NullspaceMat(uma-uma^0)[1]);
  # adjust the second row relative to the first
  if T[2][1] <> 0*one then
    tmp := T[1][1]*(uma[1][1]-1) + T[1][2]*uma[2][1];
    T[2] := T[2]/T[2][1]*tmp;
  else
    tmp := T[1][1]*uma[1][2] + T[1][2]*(uma[2][2]-1);
    T[2] := T[2]/T[2][2]*tmp;
  fi;
  # change basis such that T becomes diagonal; then images of standard root
  # subgroups in K are gbeta invariant
  bK := Eigenvectors(Fq, T);
  pre := GroupHomomorphismByFunction(Source(hK), Source(hK), 
                                     g-> g^bK, g->bK*g*bK^-1);
  hK := pre*hK;
        
  # the same for hh
  M := DerivedGL2(hh, q);
  hM := HomMatBlackSL2(M, q);
  # find 2x2-matrix acting on standard SL2 like galpha on M
  ua := Image(hM, genSL2[2]);
  ua := PreImageElm(hM, ua^galpha);
  uma := Image(hM, genSL2[3]);
  uma := PreImageElm(hM, uma^galpha);
  T := [NullspaceMat(ua-ua^0)[1]];
  Add(T, NullspaceMat(uma-uma^0)[1]);
  # adjust the second row relative to the first
  if T[2][1] <> 0*one then
    tmp := T[1][1]*(uma[1][1]-1) + T[1][2]*uma[2][1];
    T[2] := T[2]/T[2][1]*tmp;
  else
    tmp := T[1][1]*uma[1][2] + T[1][2]*(uma[2][2]-1);
    T[2] := T[2]/T[2][2]*tmp;
  fi;
  # change basis such that T becomes diagonal; then images of standard root
  # subgroups in M are galpha invariant
  bM := Eigenvectors(Fq, T);
  pre := GroupHomomorphismByFunction(Source(hM), Source(hM), 
                                     g-> g^bM, g->bM*g*bM^-1);
  hM := pre*hM;


  # now we can define the images of the standard generators
  # ordering of root subgroups: al, -al, be, -be, ga, -ga;
  # for each basis of F_q/F_p: 1, z^2, z^4, ..., z^(2(e-1))
  genimg := [];
  # alpha and -alpha, from SL2 and pi_alpha
  tmp := [genSL2[2]];
  for i in [1..e-1] do
    Add(tmp, genSL2[1]*tmp[i]*genSL2[1]^-1);
  od;
  Add(genimg, List(tmp, x-> Image(hK, x)));
  Add(genimg, List(tmp, x-> Image(hK, TransposedMat(x))));
  # X_beta(1) can be chosen freely, get a corresponding X_-beta(1) with hM 
  tmp := [Image(hM, genSL2[2]), Image(hM, genSL2[3])];
  if Comm(genimg[1][1], tmp[1]) = one then
    tmp := [tmp[2], tmp[1]];
  fi;
  # now X_gamma as commutator of  with X_beta(1) with X_alpha()
  genimg[5] := List(genimg[1], x-> Comm(tmp[1], x));
  # and X_-gamma
  genimg[6] := List(genimg[2], x-> Comm(x, tmp[2]));
  # X_beta
  genimg[3] := List(genimg[2], x-> Comm(genimg[5][1], x));
  # X_-beta
  genimg[4] :=  List(genimg[1], x-> Comm(x, genimg[6][1]));

  # now check the relations
  # order p
  if not ForAll(genimg, a-> ForAll(a, x-> x^p = one)) then
    Info(InfoGrpRec, 3, "root element not of order p");
    return fail;
  fi;
  # root subgroups commutative
  if not ForAll(genimg, a-> ForAll([1..e], i-> ForAll([1..i-1], j->
                Comm(a[i], a[j]) = one))) then
    Info(InfoGrpRec, 3, "root subgroups not abelian");
    return fail;
  fi;
  psi := [[1,-1,0],[-1,1,0],[0,1,-1],[0,-1,1],[1,0,-1],[-1,0,1]];
  negC := [[1,3],[3,6],[5,4],[2,5],[4,2],[6,1]];
  # commuting root subgroups
  if not ForAll([1..6], i-> ForAll(Filtered([1..6], j-> psi[i] <> - psi[j] 
    and not psi[i]+psi[j] in psi), 
    j-> ForAll(genimg[i], x-> ForAll(genimg[j], y-> x*y=y*x)))) then
    Info(InfoGrpRec, 3, "root subgroups don't commute");
    return fail;
  fi;
  # rest needs arithmetic in F_q
  z := PrimitiveRoot(Fq);
  bas := Basis(Fq, List([0..e-1], i-> z^(2*i)));
  # decompose products of basis elements into bas
  mpos := List([1..e], i-> List([1..i], j-> 
               IntVecFFE(Coefficients(bas, bas[i]*bas[j]))));
  mneg := List([1..e], i-> List([1..i], j-> 
               IntVecFFE(Coefficients(bas, -bas[i]*bas[j]))));
  for i in [1..6] do
    for j in [1..6] do
      if i<>j and psi[i] <> -psi[j] and psi[i]+psi[j] in psi then
        k := Position(psi, psi[i]+psi[j]);
        if [i,j] in negC then
          m := mneg;
        else
          m := mpos;
        fi;
        for ii in [1..e] do
          for jj in [1..ii] do
            a := Product([1..e], r-> genimg[k][r]^m[ii][jj][r]);
            if Comm(genimg[i][ii], genimg[j][jj]) <> a or
               Comm(genimg[i][jj], genimg[j][ii]) <> a then
              Info(InfoGrpRec, 3, "wrong commutator relation");
              Error();
              #return fail;
            fi;
          od;
        od;
      fi;
    od;
  od;

              
  Error();
end;

  
      
