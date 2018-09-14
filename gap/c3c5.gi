#############################################################################
##
##  semilinear.gi
##                                recog package
##                                                    Colva Rouney-Dougal
##                                                        Max Neunhoeffer
##                                                            Ákos Seress
##
##  Copyright 2006-2008 by the authors.
##  This file is free software, see license information at the end.
##
## Maybe ask Colva about this:
## This algorithm probably is based on the paper
## 'A polynomial-time reduction algorithm for groups of semilinear or subfield
## class' by Carlson, Jon F. ;Neunhöffer, Max; Roney-Dougal, Colva M. in
## J. Algebra 322 (2009), no. 3, 613–637
##
##  Handle the (projective) semilinear and subfield cases.
##
#############################################################################

RECOG.WriteOverBiggerFieldWithSmallerDegree :=
  function( inforec, gen )
    # inforec needs:
    #  bas, basi, sample, newdim, FF, d, qd from the Finder
    local i,k,newgen,row,t,val;
    gen := inforec.bas * gen * inforec.basi;
    newgen := [];  # FIXME: this will later be:
    #newgen := Matrix([],Length(inforec.sample),inforec.bas);
    for i in [1..inforec.newdim] do
        row := ListWithIdenticalEntries(inforec.newdim,Zero(inforec.FF));
        ConvertToVectorRep(row,inforec.qd);
        # FIXME: this will later be:
        # row := ZeroVector(inforec.newdim,inforec.sample);
        for k in [1..inforec.newdim] do
            val := Zero(inforec.FF);
            for t in [1..inforec.d] do
                val := gen[(i-1)*inforec.d+1][(k-1)*inforec.d+t]
                       * inforec.pows[t] + val;
            od;
            row[k] := val;
        od;
        Add(newgen,row);
# FIXME: this will go eventually:
ConvertToMatrixRep(newgen,inforec.qd);
    od;
    return newgen;
  end;

RECOG.WriteOverBiggerFieldWithSmallerDegreeFinder := function(m)
  # m a MeatAxe-module
  local F,bas,d,dim,e,fac,facs,gens,i,inforec,j,k,mp,mu,new,newgens,pr,q,v;

  if not(MTX.IsIrreducible(m)) then
      Error("cannot work for reducible modules");
  fi;
  if MTX.IsAbsolutelyIrreducible(m) = true then
      Error("cannot work for absolutely irreducible modules");
  fi;

  F := MTX.Field(m);
  q := Size(F);
  d := MTX.DegreeSplittingField(m)/DegreeOverPrimeField(F);
  e := MTX.FieldGenCentMat(m);  # in comments we call the centralising field E
  gens := MTX.Generators(m);
  dim := MTX.Dimension(m);
  # Choose the first standard basis vector as our first basis vector:
  v := ZeroVector(dim,gens[1][1]);
  v[1] := One(F);
  bas := [v]; # FIXME, this will later be:
  #bas := Matrix([v],Length(v),gens[1]);
  # Do the first E = <e>-dimension:
  for i in [1..d-1] do
      Add(bas,bas[i]*e);
  od;
  #mu := MutableBasis(F,bas);  # for membership test
  mu := rec( vectors := [], pivots := [] );
  for i in bas do
      RECOG.CleanRow(mu,ShallowCopy(i),true,fail);
  od;
  # Now we spin up but think over the vector space E:
  i := 1;
  while Length(bas) < dim do
      for j in [1..Length(gens)] do
          new := bas[i] * gens[j];
          if not(RECOG.CleanRow(mu,ShallowCopy(new),true,fail)) then
          #if not(IsContainedInSpan(mu,new)) then
              Add(bas,new);
              #CloseMutableBasis(mu,new);
              for k in [1..d-1] do
                  new := new * e;
                  RECOG.CleanRow(mu,ShallowCopy(new),true,fail);
                  Add(bas,new);
                  #CloseMutableBasis(mu,new);
              od;
          fi;
      od;
      i := i + d;
  od;
  # Since the module is irreducible i will not run over the length of bas
  # now we can write down the new action over the bigger field immediately:
# FIXME: this will later go:
# was: ConvertToMatrixRep(bas,q^d);  but this seems to be a bug!!!
ConvertToMatrixRep(bas,q);
  newgens := [];
  inforec := rec( bas := bas, basi := bas^-1, FF := GF(F,d), d := d,
                  qd := q^d );
  mp := MTX.FGCentMatMinPoly(m);
  facs := Factors(PolynomialRing(inforec.FF),mp : stopdegs := [1]);
  fac := First(facs,x->Degree(x)=1);
  pr := -(CoefficientsOfLaurentPolynomial(fac)[1][1]);
  inforec.pows := [pr^0];
  for k in [1..d-1] do
      Add(inforec.pows,inforec.pows[k]*pr);
  od;
  inforec.newdim := dim/inforec.d;
  inforec.sample := ListWithIdenticalEntries(inforec.newdim,Zero(inforec.FF));
# FIXME: this will later go:
ConvertToVectorRep(inforec.sample,inforec.qd);
  for j in [1..Length(gens)] do
      Add(newgens,RECOG.WriteOverBiggerFieldWithSmallerDegree(inforec,gens[j]));
  od;
  return rec( newgens := newgens, inforec := inforec );
end;

FindHomMethodsProjective.NotAbsolutelyIrred := function(ri,G)
  local H,f,hom,m,r;

  RECOG.SetPseudoRandomStamp(G,"NotAbsolutelyIrred");

  if IsBound(ri!.isabsolutelyirred) and ri!.isabsolutelyirred then
      # this information is coming from above
      return NeverApplicable;
  fi;

  f := ri!.field;

  # This usually comes after "ReducibleIso", which provides the following,
  # however, just to be sure:
  if not(IsBound(ri!.meataxemodule)) then
      ri!.meataxemodule := GModuleByMats(GeneratorsOfGroup(G),f);
  fi;

  m := ri!.meataxemodule;
  if MTX.IsAbsolutelyIrreducible(m) then
      return NeverApplicable;
  fi;

  Info(InfoRecog,2,"Rewriting generators over larger field with smaller",
       " degree, factor=",MTX.DegreeSplittingField(m));

  r := RECOG.WriteOverBiggerFieldWithSmallerDegreeFinder(m);
  H := GroupWithGenerators(r.newgens);
  hom := GroupHomByFuncWithData(G,H,RECOG.WriteOverBiggerFieldWithSmallerDegree,
                                r.inforec);
  SetIsInjective(hom,true);   # this only holds for matrix groups, not for
  SetIsSurjective(hom,true);  # projective groups!
                              # But as a GAP homomorphism between matrix
                              # groups, it is an isomorphism.

  # Now report back:
  SetHomom(ri,hom);

  # Hand down hint that no MeatAxe run can help:
  forfactor(ri).isabsolutelyirred := true;

  # There might be a kernel, because we have more scalars over the bigger
  # field, so go for it, however, fewer generators should suffice:
  # Also, doing normal closure will not help!
  findgensNmeth(ri).args := [5,0];
  Add(forkernel(ri).hints,
      rec( method := FindHomMethodsProjective.BiggerScalarsOnly, rank := 2000,
           stamp := "BiggerScalarsOnly" ));
  forkernel(ri).degsplittingfield := MTX.DegreeSplittingField(m)
                                   / DegreeOverPrimeField(f);
  forkernel(ri).biggerscalarsbas := r.inforec.bas;
  forkernel(ri).biggerscalarsbasi := r.inforec.basi;

  return Success;
end;

RECOG.HomBCToDiagonalBlock := function(data,x)
  local el;
  el := data.bas * x * data.basi;
  return ExtractSubMatrix(el,data.poss,data.poss);
end;

FindHomMethodsProjective.BiggerScalarsOnly := function(ri,G)
  # We come here only hinted, we project to a little square block in the
  # upper left corner and know that there is no kernel:
  local H,data,hom,newgens;
  data := rec( poss := [1..ri!.degsplittingfield],
               bas := ri!.biggerscalarsbas,
               basi := ri!.biggerscalarsbasi );
  newgens := List(GeneratorsOfGroup(G),x->RECOG.HomBCToDiagonalBlock(data,x));
  H := Group(newgens);
  hom := GroupHomByFuncWithData(G,H,RECOG.HomBCToDiagonalBlock,data);
  SetHomom(ri,hom);

  Add(forfactor(ri).hints,
      rec( method := FindHomMethodsProjective.StabilizerChain, rank := 4000,
           stamp := "StabilizerChain" ));

  findgensNmeth(ri).method := FindKernelDoNothing;

  return Success;
end;

# The following are for subfield computations:

RECOG.ScalarToMultiplyIntoSmallerField := function(m,k)
  # This assumes that m is an invertible matrix over a finite field k.
  # Returns either fail or a record r with components
  #  r.scalar
  #  r.field
  #  r.mat
  # such that r.mat = r.scalar * m and r.mat has entries in r.field
  # and r.field is a field contained in Field(m).
  local f,mm,pos,s;
  if IsPrimeField(k) then return fail; fi;
  pos := PositionNonZero(m[1]);
  s := m[1][pos]^-1;
  mm := s * m;
  f := FieldOfMatrixList([mm]);
  if k = f then return fail; fi;
  return rec( mat := mm, scalar := s, field := f );
end;

RECOG.ScalarsToMultiplyIntoSmallerField := function(l,k)
  # The same as above but for a list of matrices. Returns either fail
  # or a record:
  #  r.scalars
  #  r.newgens
  #  r.field
  local f,i,newgens,r,scalars;
  scalars := [];
  newgens := [];
  f := PrimeField(k);
  for i in [1..Length(l)] do
      r := RECOG.ScalarToMultiplyIntoSmallerField(l[i],k);
      if r = fail then return fail; fi;
      if not(IsSubset(f,r.field)) then
          f := ClosureField(f,r.field);
          if f = k then
              return fail;
          fi;
      fi;
      scalars[i] := r.scalar;
      newgens[i] := r.mat;
  od;
  return rec(scalars := scalars, newgens := newgens, field := f );
end;

RECOG.BaseChangeForSmallestPossibleField := function(grp,mtx,k)
  # grp is a matrix group over k, which must be a finite field. mtx must be
  # the GModuleByMats(GeneratorsOfGroup(grp),k).
  # The module mtx must be irreducible (not necessarily absolutely irred).
  # A subfield f of k has property (*), if and only if there
  # is an invertible matrix t with entries in k such that for every generator
  # x in gens t*x*t^-1 has entries in f.
  # Lemma: There is a smallest subfield f of k with property (*).
  # This function either returns fail (in case f=k) or returns a record r
  # with the following components:
  #   r.t       : the matrix t
  #   r.ti      : the inverse of t
  #   r.newgens : the list of generators t * x * ti
  #   r.field   : the smaller field

  local a,algel,b,bi,charPoly,deg,dim,element,f,facs,field,g,i,newgens,
        r,scalars,seb,v,w;

  f := PrimeField(k);
  MTX.IsAbsolutelyIrreducible(mtx);  # To ensure that the following works:
  deg := MTX.DegreeSplittingField(mtx)/DegreeOverPrimeField(k);

  # Now try to find an IdWord:
  element := false ;
  a := Zero(GeneratorsOfGroup(grp)[1]);
  dim := Length(a);
  while ( element = false ) do
    a := a + Random ( f ) * PseudoRandom ( grp ) ;

    # Check char. polynomial of a to make sure it lies in smallField [ x ]
    charPoly := CharacteristicPolynomial ( a ) ;
    field := Field(CoefficientsOfLaurentPolynomial(charPoly)[1]);
    if not(IsSubset(f,field)) then
        f := ClosureField(f,field);
        if Size(f) >= Size(k) then
            return fail;
        fi;
    fi;

    # FIXME: We only take factors that occur just once (good factors)!
    facs := Collected(Factors(charPoly : onlydegs := [1..3]));
    facs := Filtered(facs,x->x[2] = 1);

    i := 1;
    while i <= Length(facs) do
        algel := Value(facs[i][1],a);
        v := MutableCopyMat(NullspaceMat(algel));
        if Length(v) = deg then  # this is an IdWord!
            break;
        fi;
        i := i + 1;
    od;

    if i <= Length(facs) then   # we were successful!
        element := algel;
    fi;
  od;

  # If we have reached this position, we have an idword and now spin up:
  seb := rec( vectors := [], pivots := [] );
  b := [ShallowCopy(v[1])];
  RECOG.CleanRow(seb,v[1],true,fail);
  i := 1;
  while Length(b) < dim do
      for g in GeneratorsOfGroup(grp) do
          w := b[i] * g;
          if RECOG.CleanRow( seb, ShallowCopy(w), true, fail ) = false then
              Add(b,w);
          fi;
      od;
      i := i + 1;
  od;
  ConvertToMatrixRep(b);
  bi := b^-1;
  newgens := List(GeneratorsOfGroup(grp),x->b*x*bi);
  f := FieldOfMatrixList(newgens);
  if f = k then return fail; fi;
  return rec( newgens := newgens, field := f, t := b, ti := bi );
end;

RECOG.ForceToOtherField := function(m,fieldsize)
  local n,v,w,q;
  n := [];
  for v in m do
      w := List(v,x->x);  # this unpacks
      # Note: we used to call ConvertToVectorRep(w,fieldsize), which
      # also would save us work down the line; however, unfortunately
      # this may run into an Error instead of returning fail, so we have
      # to resort to the following, which is somewhat less efficient if
      # some rows are already defined over subfields.
      q := ConvertToVectorRep(w);
      if q = fail or (fieldsize mod q) <> 0 then
          return fail;
      fi;
      Add(n,w);
  od;
  ConvertToMatrixRep(n,fieldsize);
  return n;
end;

RECOG.HomDoBaseAndFieldChange := function(data,el)
  local m;
  m := data.t * el * data.ti;
  return RECOG.ForceToOtherField(m,Size(data.field));
end;

RECOG.HomDoBaseAndFieldChangeWithScalarFinding := function(data,el)
  local m,p;
  m := data.t * el * data.ti;
  p := PositionNonZero(m[1]);
  m := (m[1][p]^-1) * m;     # this gets rid of any possible scalar
                             # from some bigger field
  return RECOG.ForceToOtherField(m,Size(data.field));
end;

FindHomMethodsProjective.Subfield :=
  function(ri,G)
    # We assume G to be absolutely irreducible, although this is not
    # necessary:
    local Gprime,H,b,dim,f,hom,mo,newgens,pf,r;
    RECOG.SetPseudoRandomStamp(G,"Subfield");
    f := ri!.field;
    if IsPrimeField(f) then
        return false;     # nothing to do
    fi;
    if not(IsBound(ri!.meataxemodule)) then
        ri!.meataxemodule := GModuleByMats(GeneratorsOfGroup(G),f);
    fi;
    if not(MTX.IsIrreducible(ri!.meataxemodule)) then
        return false;     # not our case
    fi;
    dim := ri!.dimension;
    pf := PrimeField(f);
    b := RECOG.BaseChangeForSmallestPossibleField(G,ri!.meataxemodule,f);
    if b <> fail then
        Info(InfoRecog,2,"Conjugating group from GL(",dim,",",f,
             ") into GL(",dim,",",b.field,").");
        # Do base change isomorphism:
        H := GroupWithGenerators(b.newgens);
        hom := GroupHomByFuncWithData(G,H,RECOG.HomDoBaseAndFieldChange,b);
        SetIsInjective(hom,true);
        SetIsSurjective(hom,true);
        # Now report back, it is an isomorphism:
        SetHomom(ri,hom);
        findgensNmeth(ri).method := FindKernelDoNothing;
        return Success;
    fi;

    return false;   # nothing more to do for us, C3C5 takes care of the rest!
  end;

RECOG.HomActionFieldAuto := function(data,el)
  local pos,y;
  y := data.cgen ^ el;
  pos := Position(data.c,y);
  if pos = fail then return fail; fi;
  return data.cyc^data.cc[pos];
end;

RECOG.HomCommutator := function(data,el)
  local y;
  y := Comm(data.x,el);
  if RECOG.IsScalarMat(y) = false then return fail; fi;
  return ExtractSubMatrix(y,[1],[1]);
end;

RECOG.DecomposeNilpotent := function(data,el)
  # Assume to have data.primesfactor, data.primeskernel which are
  # disjoint sets of primes such that the order of el is a product of
  # prime powers using only primes from these two sets. The order of
  # el is computed with the function data.orderfunc.
  local a,b,f,fac,ker,o,p,r;
  o := data.orderfunc(el);
  if o = 1 then
      return [el,el,0,0];
  fi;
  f := Factors(o);
  fac := [];
  ker := [];
  for p in f do
      if p in data.primesfactor then
          Add(fac,p);
      elif p in data.primeskernel then
          Add(ker,p);
      else
          return fail;
      fi;
  od;
  a := Product(fac);
  b := Product(ker);
  # Now a and b are coprime
  r := Gcdex(a,b);
  if r.gcd <> 1 then Error("Absolutely impossible!"); fi;
  # now r.coeff1 * a + r.coeff2 * b = 1
  # that is, el = el^(r.coeff1 * a) * el^(r.coeff2 * b)
  # and el^(r.coeff1*a) has order not divisible by a prime in primesfactor
  # and el^(r.coeff2*b) has order not divisible by a prime in primeskernel
  # and the two commute,
  # that is we have found the components in the direct sum decomposition
  return [el^(r.coeff1*a),el^(r.coeff2*b),r.coeff1*a,r.coeff2*b];
end;

RECOG.HomForNilpotent := function(data,el)
  local decomp;
  decomp := RECOG.DecomposeNilpotent(data,el);
  if decomp = fail then
      return fail;
  else
      return decomp[2];
  fi;
end;

RECOG.ProjectiveOrder := function(el)
  return ProjectiveOrder(el)[1];
end;

RECOG.CalcNiceGensKnownNilpotent := function(ri,origgens)
  local b;
  b := List([1..Length(ri!.waytonice)],i->origgens[i]^ri!.waytonice[i][1]);
  return Concatenation(CalcNiceGens(RIFac(ri),origgens),
                       CalcNiceGens(RIKer(ri),b));
end;

FindHomMethodsProjective.KnownNilpotent := function(ri,G)
  # Hint to this method if you know G to be nilpotent or call it directly
  # if you find out so. Note that it will return NeverApplicable if G is a p-group
  # for some prime p. Make sure that the !.projective component is set
  # correctly such that we can set the right Order method.
  local H,cut,data,gens,gens2,gensfac,gensker,gensm,hom,orderfunc,ords,primes;
  gens := GeneratorsOfGroup(G);
  gensm := GeneratorsWithMemory(gens);
  if ri!.projective then
      orderfunc := RECOG.ProjectiveOrder;
  else
      orderfunc := Order;
  fi;
  if IsBound(ri!.primes) then    # this is a message from ourselves from above!
      primes := ri!.primes;
  else
      ords := List(gens,orderfunc);
      primes := Union(List(ords,o->Set(Factors(o))));
      RemoveSet(primes,1);    # in case there were identities!
  fi;
  if Length(primes) < 2 then return NeverApplicable; fi;   # not our beer
  cut := QuoInt(Length(primes),2);
  data := rec( primesfactor := primes{[1..cut]},
               primeskernel := primes{[cut+1..Length(primes)]},
               orderfunc := orderfunc );
  gens2 := List(gensm,x->RECOG.DecomposeNilpotent(data,x));
  gensfac := List(gens2,x->StripMemory(x[2]));
  gensker := List(gens2,x->x[1]);
  ri!.waytonice := List(gens2,x->x{[3,4]});
  H := GroupWithGenerators(gensfac);
  hom := GroupHomByFuncWithData(G,H,RECOG.HomForNilpotent,data);
  SetHomom(ri,hom);
  forfactor(ri).primes := primes{[1..cut]};
  forkernel(ri).primes := primes{[cut+1..Length(primes)]};
  Add(forfactor(ri).hints,
      rec( method := FindHomMethodsProjective.KnownNilpotent, rank := 4000,
           stamp := "KnownNilpotent" ));
  Add(forkernel(ri).hints,
      rec( method := FindHomMethodsProjective.KnownNilpotent, rank := 4000,
           stamp := "KnownNilpotent" ));
  Append(gensN(ri),gensker);
  findgensNmeth(ri).method := FindKernelDoNothing;  # kernel already known
  ri!.leavegensNuntouched := true;
  Setcalcnicegens(ri,RECOG.CalcNiceGensKnownNilpotent);
  return Success;
end;

FindHomMethodsProjective.FewGensAbelian := function(ri,G)
  # If the number of generators is less than or equal to 200, then check
  # abelian and if so, hint to KnownNilpotent to write it as a direct
  # product of Sylow subgroups
  local gens,i,j,l;
  gens := GeneratorsOfGroup(G);
  l := Length(gens);
  if l > 200 then return NeverApplicable; fi;
  for i in [1..l-1] do
      for j in [i+1..l] do
          if not(ri!.isequal(gens[i]*gens[j],gens[j]*gens[i])) then
              return NeverApplicable;
          fi;
      od;
  od;
  # We call KnownNilpotent:
  return FindHomMethodsProjective.KnownNilpotent(ri,G);
end;


FindHomMethodsProjective.C3C5 := function(ri,G)
  # We assume that G acts absolutely irreducibly and that the matrix group
  # G cannot be realised over a smaller field. However, it might still be
  # C3 or C5. We see what we can do by computing a normal subgroup of
  # the derived subgroup...
  local H,HH,Hgens,a,b,basis,c,cc,cgen,collf,coms,conjgensG,cyc,deg,dim,
        f,g,gens,gensim,hom,homcomp,homs,homsimg,i,j,kro,m,newgens,nr,o,
        pf,pos,pr,pr2,q,r,scalar,subdim,x,poss;

  RECOG.SetPseudoRandomStamp(G,"C3C5");

  f := ri!.field;
  if not(IsBound(ri!.meataxemodule)) then
      ri!.meataxemodule := GModuleByMats(GeneratorsOfGroup(G),f);
  fi;
  if not(MTX.IsIrreducible(ri!.meataxemodule)) then
      return NeverApplicable;     # not our case
  fi;
  dim := ri!.dimension;
  pf := PrimeField(f);

  # First compute a few random commutators:
  coms := [];
  scalar := true;   # as we go, we check whether something is non-scalar
  for i in [1..10] do
      x := Comm(PseudoRandom(G),PseudoRandom(G));
      Add(coms,x);
      if RECOG.IsScalarMat(x) = false then scalar := false; fi;
  od;
  # Let N to be the normaliser of Group(coms) in G, N is a normal subgroup
  # of G which is contained in G'.
  gens := GeneratorsOfGroup(G);
  if scalar then    # we highly suspect that G' is scalar, in this case,
                    # we want to find a non-scalar element such that the
                    # commutators with all generators are scalar, this
                    # gives us a reduction, regardless whether G' is in
                    # fact scalar or not!
      Info( InfoRecog, 3, "Suspect that G' is scalar, checking..." );
      i := 1;
      while RECOG.IsScalarMat(gens[i]) <> false do
          i := i + 1;
      od;
      # It cannot happen that all matrices are scalar, because then
      # we would not be absolutely irreducible!
      # Now gens[i] is not central, since then the action would not
      # be absolutely irreducible!
      j := 1;
      while j <= Length(gens) do
          if j <> i then
              x := Comm(gens[i],gens[j]);
              if RECOG.IsScalarMat(x) = false then
                  Add(coms,x);
                  scalar := false;
                  Info( InfoRecog, 3, "NO! G' is not scalar after all!" );
                  break;
              fi;
          fi;
          j := j + 1;
      od;
      if scalar then   # otherwise fall through and go on
          # gens[i] is not central but all Comm(gens[i],gens[j]) are.
          Info( InfoRecog, 2, "We found a homomorphism by commutators." );
          r := rec( x := gens[i] );
          gensim := List(gens,x->RECOG.HomCommutator(r,x));
          H := GroupWithGenerators(gensim);
          hom := GroupHomByFuncWithData(G,H,RECOG.HomCommutator,r);
          SetHomom(ri,hom);
          Setmethodsforfactor(ri,FindHomDbMatrix);
          poss := Filtered([1..Length(gensim)],i->IsOne(gensim[i]));
          Append(gensN(ri),ri!.gensHmem{poss});
          findgensNmeth(ri).args[1] := 5;
          return Success;
      fi;
  fi;

  # Now we compute O(d*log(q)+log(d)) random elements of the normaliser in G
  # of the group generated by coms:
  pr2 := ProductReplacer(GeneratorsOfGroup(G),rec(noaccu := true));
  pr := ProductReplacer(coms,rec(normalin := pr2));
  nr := Minimum(Maximum(5,QuoInt(dim*Log2Int(Size(f)),20)),40);
  Info( InfoRecog, 3, "C3C5: computing ",nr," generators for N...");
  Hgens := ShallowCopy(coms);
  for i in [1..nr] do
      Add(Hgens,Next(pr));
  od;
  H := GroupWithGenerators(Hgens);
  # Now H is with very high probability a subgroup of N which has the
  # same orbits as N on one-dimensional subspaces and thus the same
  # submodule lattice as N in the natural module.

  m := GModuleByMats(Hgens,f);

  # Here comes the great case distinction: We branch according to the
  # behaviour of m:
  if MTX.IsIrreducible(m) then
      # In this case m is either absolutely irreducible or not.
      # If so, C3 is impossible and we can test C5 for G, since H has lost
      # the "dirty scalars". If G is not C5, we fail.
      # If not, we know that G is C3 and this is exhibited by H. We
      # still can test for C5 if we wish.
      # So, we first test for C5 in either case and only if this does not
      # work we settle C3:

      if not(IsPrimeField(f)) then
          b := RECOG.BaseChangeForSmallestPossibleField(H,m,f);
          if b <> fail then   # Yes! N is realisable!
                Info(InfoRecog,2,"Can conjugate H subgroup from GL(",dim,
                     ",",f,") into GL(",dim,",",b.field,").");
                # Now do base change for generators of G:
              newgens := List(gens,x->b.t*x*b.ti);
              r := RECOG.ScalarsToMultiplyIntoSmallerField(newgens,f);
              if r <> fail then   # Yes again! This works!
                  Info(InfoRecog,2,"Conjugating group from GL(",dim,",",f,
                       ") into GL(",dim,",",r.field,").");

                  # Set up an isomorphism:
                  H := GroupWithGenerators(newgens);
                  hom := GroupHomByFuncWithData(G,H,
                           RECOG.HomDoBaseAndFieldChangeWithScalarFinding,b);
                  # Now report back, it is an isomorphism, because this is a
                  # projective method:
                  SetHomom(ri,hom);
                  findgensNmeth(ri).method := FindKernelDoNothing;
                  return Success;
              fi;
          fi;
      fi;
      # We now know that G is not C5!
      Info(InfoRecog,2,"G is not C5 (subfield).");

      # Check whether m is not absolutely irreducible, then G is C3,
      # otherwise not!
      if MTX.IsAbsolutelyIrreducible(m) then
          # We fail, G is neither C3 nor C5, and we do not find a way
          # for any reduction using H:
          Info(InfoRecog,2,"G is not C3 (semilinear).");
          return NeverApplicable;
      fi;

      # Now G is C3, so we have to compute the action of G on the
      # centralising matrices of H!

      c := [MTX.FieldGenCentMat(m)];
      deg := MTX.DegreeSplittingField(m) / DegreeOverPrimeField(f);
      # The centralising field C is a field extension of f if this
      # degree, thus, Gal(C/f) is cyclic of order deg, generated
      # by the Frobenius automorphism mapping x -> x^|f|.
      q := Size(f);
      for i in [1..deg-1] do
          c[i+1] := c[i]^q;
      od;
      cc := [0..deg-1];
      cgen := c[1];
      SortParallel(c,cc);
      gensim := [];
      cyc := PermList(Concatenation([2..deg],[1]));
      for g in gens do
          x := cgen^g;
          pos := Position(c,x);
          if pos = fail then   # something is wrong!
              Info( InfoRecog, 1, "Sudden failure, G should be C3 but isn't! ",
                    "C3C5 gives up for the moment." );
              return TemporaryFailure;
          fi;
          Add(gensim,cyc^cc[pos]);
      od;
      Info( InfoRecog, 2, "G is C3, found action as field auts of size ",
            deg,".");
      HH := GroupWithGenerators(gensim);
      hom := GroupHomByFuncWithData(G,HH,RECOG.HomActionFieldAuto,
                  rec( c := c,cc := cc,cgen := cgen, cyc := cyc ) );
      SetHomom(ri,hom);
      Setmethodsforfactor(ri,FindHomDbPerm);
      return Success;

      # The kernel will be semilinear directly, however, we have to
      # run the MeatAxe again, so give no hint!

  else   # m is reducible
      # In this case we find a reduction, however, there are 2 different
      # cases (since H is supposed to behave like N, we can use Clifford's
      # theorem):
      #   - there is more than one homogeneous component:
      #     then we act with G on them, the kernel will be reducible
      #   - there is exactly one homogeneous component and the dimension
      #     of the irreducible H-submodule is more than 1:
      #     then we find a tensor decomposition
      # Note that this dimension is >1 since we have ruled out H to
      # be scalar already!
      collf := MTX.CollectedFactors(m);
      if Length(collf) = 1 then    # only one homogeneous component!
          if MTX.Dimension(collf[1][1]) = 1 then
              Error("This should never have happened (2), tell Max.");
              # This should have been caught by the scalar test above.
          fi;
          Info(InfoRecog,2,"Restriction to H is homogeneous.");
          if not(MTX.IsAbsolutelyIrreducible(collf[1][1])) then
              Error("Is this really possible??? G acts absolutely irred!");
          fi;
          homs := MTX.Homomorphisms(collf[1][1],m);
          basis := Concatenation(homs);
          ConvertToMatrixRep(basis,Size(f));
          subdim := MTX.Dimension(collf[1][1]);
          r := rec(t := basis, ti := basis^-1,
                   blocksize := MTX.Dimension(collf[1][1]));
          # Note that we already checked for semilinear, so we know that
          # the irreducible N-submodule is absolutely irreducible!
          # Now we believe to have a tensor decomposition:
          conjgensG := List(gens,x->r.t * x * r.ti);
          kro := List(conjgensG,g->RECOG.IsKroneckerProduct(g,r.blocksize));
          if not(ForAll(kro,k->k[1] = true)) then
              Info(InfoRecog,1,"VERY, VERY, STRANGE!");
              Info(InfoRecog,1,"False alarm, was not a tensor decomposition.");
              Error("This should never have happened (3), tell Max.");
          fi;

          H := GroupWithGenerators(conjgensG);
          hom := GroupHomByFuncWithData(G,H,RECOG.HomDoBaseChange,r);
          SetHomom(ri,hom);

          # Hand down information:
          forfactor(ri).blocksize := r.blocksize;
          forfactor(ri).generatorskronecker := kro;
          Add( forfactor(ri).hints,
               rec( method := FindHomMethodsProjective.KroneckerProduct,
                    rank := 4000, stamp := "KroneckerProduct" ) );
          # This is an isomorphism:
          findgensNmeth(ri).method := FindKernelDoNothing;
          return Success;
      fi;
      Info(InfoRecog,2,"Using action on the set of homogeneous components",
           " (",Length(collf)," elements)...");
      # Now find a homogeneous component to act on it:
      homs := MTX.Homomorphisms(collf[1][1],m);
      homsimg := BasisVectors(Basis(VectorSpace(f,Concatenation(homs))));
      homcomp := MutableCopyMat(homsimg);
      # FIXME: This will go:
      ConvertToMatrixRep(homcomp,Size(f));
      TriangulizeMat(homcomp);
      o := Orb(G,homcomp,OnSubspacesByCanonicalBasis,rec(storenumbers := true));
      Enumerate(o);
      a := OrbActionHomomorphism(G,o);
      SetHomom(ri,a);
      Setmethodsforfactor(ri,FindHomDbPerm);

      return Success;

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

