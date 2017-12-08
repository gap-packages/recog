#############################################################################
##
##  semilinear.gi
##                                recog package
##                                                        Max Neunhoeffer
##                                                            Ákos Seress
##
##  Copyright 2006-2008 by the authors.
##  This file is free software, see license information at the end.
##
##  Handle the (projective) semilinear case.
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
        row := ZeroVector(inforec.newdim,inforec.sample);
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

  d := MTX.DegreeSplittingField(m);
  e := MTX.FieldGenCentMat(m);  # in comments we call the centralising field E
  gens := MTX.Generators(m);
  F := MTX.Field(m);
  q := Size(F);
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
ConvertToMatrixRep(bas,q^d);
  newgens := [];
  inforec := rec( bas := bas, basi := bas^-1, FF := GF(F,d), d := d,
                  qd := q^d );
  mp := MTX.FGCentMatMinPoly(m);
  facs := Factors(PolynomialRing(inforec.FF),mp : stopdegs := [1]);
  fac := First(facs,x->Degree(x)=1);
  pr := -(CoefficientsOfLaurentPolynomial(fac)[1][1]);
  inforec.pows := [pr^0];
  for k in [1..d-1] do Add(inforec.pows,inforec.pows[k]*pr); od;
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

  if IsBound(ri!.isabsolutelyirred) and ri!.isabsolutelyirred then
      # this information is coming from above
      return false;
  fi;

  f := ri!.field;

  # Just to be sure:
  if not(IsBound(ri!.meataxemodule)) then
      ri!.meataxemodule := GModuleByMats(GeneratorsOfGroup(G),f);
  fi;

  # this usually comes after "ReducibleIso", which provides the following:
  m := ri!.meataxemodule;
  if MTX.IsAbsolutelyIrreducible(m) then
      return false;
  fi;

  Info(InfoRecog,2,"Rewriting generators over larger field with smaller",
       " degree, factor=",MTX.DegreeSplittingField(m));

  r := RECOG.WriteOverBiggerFieldWithSmallerDegreeFinder(m);
  H := GroupWithGenerators(r.newgens);
  hom := GroupHomByFuncWithData(G,H,RECOG.WriteOverBiggerFieldWithSmallerDegree,
                                r.inforec);
  SetIsInjective(hom,true);   # this only holds for matrix groups, not for
  SetIsSurjective(hom,true);  # projective groups!

  # Now report back:
  SetHomom(ri,hom);

  # Hand down hint that no MeatAxe run can help:
  forfactor(ri).isabsolutelyirred := true;

  # There might be a kernel, because we have more scalars over the bigger
  # field, so go for it, however, some more generators might be in order,
  # Normal closure however is unnecessary.
  findgensNmeth(ri).args[1] := 5;
  findgensNmeth(ri).args[2] := 0;
  Add(forkernel(ri).hints,
      rec( method := FindHomMethodsProjective.BiggerScalarsOnly, rank := 2000,
           stamp := "BiggerScalarsOnly" ));
  forkernel(ri).degsplittingfield := MTX.DegreeSplittingField(m)
                                   / DegreeOverPrimeField(f);

  return true;
end;

FindHomMethodsProjective.BiggerScalarsOnly := function(ri,G)
  # We come here only hinted, we project to a little square block in the
  # upper left corner and know that there is no kernel:
  local H,data,hom,newgens;
  data := rec( poss := [1..ri!.degsplittingfield] );
  newgens := List(GeneratorsOfGroup(G),x->RECOG.HomToDiagonalBlock(data,x));
  H := Group(newgens);
  hom := GroupHomByFuncWithData(G,H,RECOG.HomToDiagonalBlock,data);
  SetHomom(ri,hom);

  Add(forfactor(ri).hints,
      rec( method := FindHomMethodsProjective.StabilizerChain, rank := 4000,
           stamp := "StabilizerChain" ));

  findgensNmeth(ri).method := FindKernelDoNothing;

  return true;
end;

FindHomMethodsProjective.C3C5 := function(ri,G)
  # We assume that G acts absolutely irreducibly and see what we can
  # do by computing a normal subgroup of the derived subgroup.

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

