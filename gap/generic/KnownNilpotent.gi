#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This files's authors include Max Neunhöffer, Ákos Seress, Max Horn.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
#############################################################################

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
  if r.gcd <> 1 then
      ErrorNoReturn("<data> corrupt, Product(<data.primesfactor>) and ",
                    "Product(<data.primeskernel>) are not coprime");
  fi;
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

RECOG.CalcNiceGensKnownNilpotent := function(ri,origgens)
  local kernelgens;
  kernelgens := List([1..Length(ri!.decompositionExponents)],
                     i -> origgens[i]^ri!.decompositionExponents[i]);
  return Concatenation(CalcNiceGens(ImageRecogNode(ri), origgens),
                       CalcNiceGens(KernelRecogNode(ri), kernelgens));
end;

#! @BeginChunk KnownNilpotent
#! Hint to this method if you know G to be nilpotent or call it directly
#! if you find out so. Note that it will return NeverApplicable if G is a
#! p-group for some prime p. Make sure that the !.projective component is set
#! correctly such that we can set the right Order method.
#! @EndChunk
BindRecogMethod(FindHomMethodsGeneric, "KnownNilpotent",
"method for nilpotent groups which are not p-groups",
function(ri,G)
  local H,cut,data,gens,decompositionData,gensfac,gensker,gensm,hom,ords,primes;
  gens := GeneratorsOfGroup(G);
  gensm := GeneratorsWithMemory(gens);
  if IsBound(ri!.primes) then    # this is a message from ourselves from above!
      primes := ri!.primes;
  else
      ords := List(gens,OrderFunc(ri));
      primes := Union(List(ords,o->Set(Factors(o))));
      RemoveSet(primes,1);    # in case there were identities!
  fi;
  if Length(primes) < 2 then
      return NeverApplicable;   # not our beer
  fi;
  cut := QuoInt(Length(primes),2);
  data := rec( primesfactor := primes{[1..cut]},
               primeskernel := primes{[cut+1..Length(primes)]},
               orderfunc := OrderFunc(ri) );
  decompositionData := List(gensm, x-> RECOG.DecomposeNilpotent(data,x));
  gensfac := List(decompositionData,x -> StripMemory(x[2]));
  gensker := List(decompositionData,x -> x[1]);
  ri!.decompositionExponents := List(decompositionData, x -> x[3]);
  H := GroupWithGenerators(gensfac);
  hom := GroupHomByFuncWithData(G,H,RECOG.HomForNilpotent,data);
  SetHomom(ri,hom);
  InitialDataForImageRecogNode(ri).primes := primes{[1..cut]};
  InitialDataForKernelRecogNode(ri).primes := primes{[cut+1..Length(primes)]};
  AddMethod(InitialDataForImageRecogNode(ri).hints, FindHomMethodsGeneric.KnownNilpotent, 4000);
  AddMethod(InitialDataForKernelRecogNode(ri).hints, FindHomMethodsGeneric.KnownNilpotent, 4000);
  Append(gensN(ri),gensker);
  findgensNmeth(ri).method := FindKernelDoNothing;  # kernel already known
  ri!.leavegensNuntouched := true;
  Setcalcnicegens(ri,RECOG.CalcNiceGensKnownNilpotent);
  return Success;
end);
