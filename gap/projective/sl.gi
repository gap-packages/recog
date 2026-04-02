#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This files's authors include Max Neunhöffer, Ákos Seress.
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
##  This is the SL_n code by Ákos and Max, the precursor for Daniel's code.
##  Thus it will become unused once we switch to Daniel's code.
##
#############################################################################


# TODO: which algorithm is this? reference?
RECOG.FindStdGens_SL := function(sld)
  # gens of sld must be gens for SL(d,q) in its natural rep with memory
  # This function calls RECOG.SLn_constructsl2 and then extends
  # the basis to a basis of the full row space and calls
  # RECOG.SLn_UpStep often enough. Finally it returns an slp such
  # that the SL(d,q) standard generators with respect to this basis are
  # expressed by the slp in terms of the original generators of sld.
  local V,b,bas,basi,basit,d,data,ext,fakegens,id,nu,nu2,p,q,resl2,sl2,sl2gens,
        sl2gensf,sl2genss,sl2stdf,slp,slpsl2std,slptosl2,st,std,stdgens,i,ex,f;

  # Some setup:
  f := FieldOfMatrixGroup(sld);
  p := Characteristic(f);
  q := Size(f);
  ext := DegreeOverPrimeField(f);
  d := DimensionOfMatrixGroup(sld);
  if not IsObjWithMemory(GeneratorsOfGroup(sld)[1]) then
      sld := GroupWithMemory(sld);
  fi;

  # First find an SL2 with the space it acts on:
  Info(InfoRecog,2,"Finding an SL2...");
  data := RECOG.SLn_constructsl2(sld,d,q);

  bas := ShallowCopy(BasisVectors(Basis(data[2])));
  sl2 := data[1];
  slptosl2 := SLPOfElms(GeneratorsOfGroup(sl2));
  sl2gens := StripMemory(GeneratorsOfGroup(sl2));
  V := data[2];
  b := Basis(V,bas);
  sl2genss := List(sl2gens,x->RECOG.LinearAction(b,f,x));

  if q in [2,3,4,5,9] then
      Info(InfoRecog,2,"In fact found an SL4...");
      stdgens := RECOG.MakeSL_StdGens(p,ext,4,4).all;
      slpsl2std := RECOG.FindStdGensUsingBSGS(Group(sl2genss),stdgens,
                                              false,false);
      nu := List(sl2gens,x->NullspaceMat(x-One(x)));
      ex := SumIntersectionMat(nu[1],nu[2])[2];
      for i in [3..Length(nu)] do
          ex := SumIntersectionMat(nu[3],ex);
      od;
      Append(bas,ex);
      ConvertToMatrixRep(bas,q);
      basi := bas^-1;
  else
      # Now compute the natural SL2 action and run constructive recognition:
      Info(InfoRecog,2,
           "Recognising this SL2 constructively in 2 dimensions...");
      sl2genss := GeneratorsWithMemory(sl2genss);
      resl2 := RECOG.ConRecogNaturalSL2(Group(sl2genss),f);
      slpsl2std := SLPOfElms(resl2.all);
      bas := resl2.bas * bas;
      # We need the actual transvections:
      slp := SLPOfElms([resl2.s[1],resl2.t[1]]);
      st := ResultOfStraightLineProgram(slp,
                                        StripMemory(GeneratorsOfGroup(sl2)));

      # Extend basis by something invariant under SL2:
      id := IdentityMat(d,f);
      nu := NullspaceMat(StripMemory(st[1]-id));
      nu2 := NullspaceMat(StripMemory(st[2]-id));
      Append(bas,SumIntersectionMat(nu,nu2)[2]);
      ConvertToMatrixRep(bas,q);
      basi := bas^-1;
  fi;

  # Now set up fake generators for keeping track what we do:
  fakegens := ListWithIdenticalEntries(Length(GeneratorsOfGroup(sld)),1);
  fakegens := GeneratorsWithMemory(fakegens);
  sl2gensf := ResultOfStraightLineProgram(slptosl2,fakegens);
  sl2stdf := ResultOfStraightLineProgram(slpsl2std,sl2gensf);
  std := rec( f := f, d := d, n := 2, bas := bas, basi := basi,
              sld := sld, sldf := fakegens, slnstdf := sl2stdf,
              p := p, ext := ext );
  Info(InfoRecog,2,"Going up to SL_d again...");
  while std.n < std.d do
      RECOG.SLn_UpStep(std);
  od;
  return rec( slpstd := SLPOfElms(std.slnstdf),
              bas := std.bas, basi := std.basi );
end;





# The going down method:

#Version 1.2

# finds first element of a list that is relative prime to all others
# input: list=[SL(d,q), d, q, SL(n,q)] acting as a subgroup of some big SL(n,q)
# output: list=[rr, dd] for a ppd(2*dd;q)-element rr
RECOG.SLn_godown:=function(list)
  local d, first, q, g, gg, i, r, pol, factors, degrees, newdim, power, rr, ss,
  newgroup, colldegrees, exp, count;

  first:=function(list)
  local i;

  for i in [1..Length(list)] do
      if list[i]>1 and Gcd(list[i],Product(list)/list[i])=1 then
         return list[i];
      fi;
  od;

  return fail;
  end;

  g:=list[1];
  d:=list[2];
  q:=list[3];
  gg:=list[4];

  Info(InfoRecog,2,"Dimension: ",d);
  #find an element with irreducible action of relative prime dimension to
  #all other invariant subspaces
  #count is just safety, if things go very bad
  count:=0;

  repeat
     count:=count+1;
  if InfoLevel(InfoRecog) >= 3 then Print(".\c"); fi;
     r:=PseudoRandom(g);
     pol:=CharacteristicPolynomial(r);
     factors:=Factors(pol);
     degrees:=AsSortedList(List(factors,Degree));
     newdim:=first(degrees);
  until (count>10) or (newdim <> fail and newdim<=Maximum(2,d/4));

  if count>10 then
     return fail;
  fi;

  # raise r to a power so that acting trivially outside one invariant subspace
  degrees:=Filtered(degrees, x->x<>newdim);
  colldegrees:=Collected(degrees);
  power:=Lcm(List(degrees, x->q^x-1))*q;
  # power further to cancel q-part of element order
  if degrees[1]=1 then
     exp:=colldegrees[1][2]-(DimensionOfMatrixGroup(gg)-d);
     if exp>0 then
       power:=power*q^exp;
     fi;
  fi;
  rr:=r^power;

  #conjugate rr to hopefully get a smaller dimensional SL
  #ss:=rr^PseudoRandom(gg);
  #newgroup:=Group(rr,ss);

  return [rr,newdim];
end;

# input is (group,dimension,q)
# output is a group element acting irreducibly in two dimensions, and fixing
# a (dimension-2)-dimensional subspace
RECOG.SLn_constructppd2:=function(g,dim,q)
  local out, list ;

  list:=[g,dim,q,g];
  repeat
     out:=RECOG.SLn_godown(list);
     if out=fail or out[1]*out[1]=One(out[1]) then
        if InfoLevel(InfoRecog) >= 3 then Print("B\c"); fi;
        list:=[g,dim,q,g];
        out:=fail;
     else
        if out[2]>2 then
           list:=[Group(out[1],out[1]^PseudoRandom(g)),2*out[2],q,g];
        fi;
     fi;
  until out<>fail and out[2]=2;

  return out[1];

end;

RECOG.SLn_constructsl4:=function(g,dim,q,r)
  local s,h,count,readydim4,readydim3,ready,u,orderu,
        nullr,nulls,nullspacer,nullspaces,int,intbasis,nullintbasis,
        newu,newbasis,newbasisinv,newr,news,outputu,mat,i,shorts,shortr;
  nullr:=NullspaceMat(StripMemory(r)-One(StripMemory(r)));
  nullspacer:=VectorSpace(GF(q),nullr);
  mat:=One(r);
  ready:=false;
  repeat
    s:=r^PseudoRandom(g);
    nulls:=NullspaceMat(StripMemory(s)-One(StripMemory(s)));
    nullspaces:=VectorSpace(GF(q),nulls);
    int:=Intersection(nullspacer,nullspaces);
    intbasis:=Basis(int);
    newbasis:=[];
    for i in [1..Length(intbasis)] do
        Add(newbasis,intbasis[i]);
    od;
    i:=0;
    repeat
       i:=i+1;
       if not mat[i] in int then
          Add(newbasis,mat[i]);
          int:=VectorSpace(GF(q),newbasis);
       fi;
    until Dimension(int)=dim;
    ConvertToMatrixRep(newbasis);
    newbasisinv:=newbasis^(-1);
    newr:=newbasis*r*newbasisinv;
    news:=newbasis*s*newbasisinv;

    #shortr, shorts do not need memory
    #we shall throw away the computations in h
    #check that we have SL(4,q), by non-constructive recognition
    shortr:=newr{[dim-3..dim]}{[dim-3..dim]};
    shorts:=news{[dim-3..dim]}{[dim-3..dim]};
    h:=Group(shortr,shorts);
    count:=0;
    readydim4:=false;
    readydim3:=false;
    repeat
       u:=PseudoRandom(h);
       orderu:=Order(u);
       if orderu mod ((q^4-1)/(q-1)) = 0 then
          readydim4:=true;
       elif Gcd(orderu,(q^2+q+1)/Gcd(3,q-1))>1 then
          readydim3:=true;
       fi;
       if readydim4 = true and readydim3 = true then
          ready:=true;
          break;
       fi;
       count:=count+1;
    until count=30;
  until ready=true;

  return Group(r,s);
end;


#g=SL(d,q), given as a subgroup of SL(dim,q)
#output: [SL(2,q), and a basis for the 2-dimensional subspace where it acts
RECOG.SLn_godownfromd:=function(g,q,d,dim)
  local y,yy,ready,order,es,dims,subsp,z,x,a,b,c,h,vec,vec2,
  pol,factors,degrees,comm1,comm2,comm3,image,basis,action,vs,readyqpl1,
  readyqm1,count,u,orderu;

  repeat
    ready:=false;
    y:=PseudoRandom(g);
    pol:=CharacteristicPolynomial(y);
    factors:=Factors(pol);
    degrees:=List(factors,Degree);
    if d-1 in degrees then
       order:=Order(y);
       if order mod (q-1)=0 then
          yy:=y^(order/(q-1));
       else
          yy:=One(y);
       fi;
       if not IsOne(yy) then
            es:= Eigenspaces(GF(q),yy);
            dims:=List(es,Dimension);
            if IsSubset(Set([1,d-1,dim-d]),Set(dims)) and
               (1 in Set(dims)) then
               es:=Filtered(es,x->Dimension(x)=1);
               vec:=Basis(es[1])[1];
               if vec*yy=vec then
                  vec:=Basis(es[2])[1];
               fi;
               repeat
                  z:=PseudoRandom(g);
                  x:=yy^z;
                  a:=Comm(x,yy);
                  b:=a^yy;
                  c:=a^x;
                  comm1:= Comm(a,c);
                  comm2:=Comm(a,b);
                  comm3:=Comm(b,c);
                  if comm1<>One(a) and comm2<>One(a) and
                    comm3<>One(a) and Comm(comm1,comm2)<>One(a) then
                    vec2:=vec*z;
                    vs:=VectorSpace(GF(q),[vec,vec2]);
                    basis:=Basis(vs);
                    #check that the action in 2 dimensions is SL(2,q)
                    #by non-constructive recognition, finding elements of
                    #order (q-1) and (q+1)
                    #we do not need memory in the group image
                    action:=List([a,b,c],x->RECOG.LinearAction(basis,q,x));
                    image:=Group(action);
                    count:=0;
                    readyqpl1:=false;
                    readyqm1:=false;
                    repeat
                       u:=PseudoRandom(image);
                       orderu:=Order(u);
                       if orderu = q-1 then
                          readyqm1:=true;
                       elif orderu = q+1 then
                          readyqpl1:=true;
                       fi;
                       if readyqm1 = true and readyqpl1 = true then
                          ready:=true;
                          break;
                       fi;
                       count:=count+1;
                     until count=20;
                  fi;
               until ready=true;
            fi;
       fi;
    fi;
  until ready;

  h:=Group(a,b,c);
  subsp:=VectorSpace(GF(q),[vec,vec2]);
  return [h,subsp];

end;

#going down from 4 to 2 dimensions, when q=2,3,4,5,9
#just construct the 4-dimensional invariant space and generators
#for the group acting on it
RECOG.SLn_exceptionalgodown:=function(h,q,dim)
  local basis, v, vs, i, gen;

  vs:=VectorSpace(GF(q),One(h));
  basis:=[];
  repeat
     if InfoLevel(InfoRecog) >= 3 then Print("C"); fi;
     for i in [1..4] do
        v:=PseudoRandom(vs);
        for gen in GeneratorsOfGroup(h) do
           Add(basis,v*gen-v);
        od;
     od;
     basis:=ShallowCopy(SemiEchelonMat(basis).vectors);
  until Length(basis)=4;
  return [h,VectorSpace(GF(q),basis)];
end;


RECOG.SLn_constructsl2:=function(g,d,q)
  local r,h;

  r:=RECOG.SLn_constructppd2(g,d,q);
  h:=RECOG.SLn_constructsl4(g,d,q,r);
  if not (q in [2,3,4,5,9]) then
     return RECOG.SLn_godownfromd(h,q,4,d);
  else
     return RECOG.SLn_exceptionalgodown(h,q,d);
  #   return ["sorry only SL(4,q)",h];
  fi;
end;

# Now the going up code:

RECOG.LinearAction := function(bas,field,el)
  local mat,vecs;
  if IsGroup(el) then
      return Group(List(GeneratorsOfGroup(el),
                        x->RECOG.LinearAction(bas,field,x)));
  fi;
  if IsBasis(bas) then
      vecs := BasisVectors(bas);
  else
      vecs := bas;
      bas := Basis(VectorSpace(field,bas),bas);
  fi;
  mat := List(vecs,v->Coefficients(bas,v*el));
  ConvertToMatrixRep(mat,field);
  return mat;
end;

RECOG.SLn_UpStep := function(w)
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
  local DoColOp_n,DoRowOp_n,FixSLn,Fixc,MB,Vn,Vnc,aimdim,c,c1,c1f,cf,cfi,
        ci,cii,coeffs,flag,i,id,int1,int3,j,k,lambda,list,mat,newbas,newbasf,
        newbasfi,newbasi,newdim,newpart,perm,pivots,pivots2,pos,pow,s,sf,
        slp,std,sum1,tf,trans,transd,transr,v,vals,zerovec;

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
        ErrorNoReturn("either i or j must be equal to n");
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
        ErrorNoReturn("either i or j must be equal to n");
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
          ErrorNoReturn("this program only works for odd n or n=2");
      fi;
  else
      # In this case the n-1-cycle is the identity, so we take a transvection:
      s := MutableCopyMat(id);
      s[1,2] := One(w.f);
      sf := w.slnstdf[1];
  fi;

  # Find a good random element:
  w.count := 0;
  aimdim := Minimum(2*w.n-1,w.d);
  newdim := aimdim - w.n;
  while true do   # will be left by break
      while true do    # will be left by break
          if InfoLevel(InfoRecog) >= 3 then Print(".\c"); fi;
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
                  Info(InfoRecog,2,"Ooops: Component n was zero!");
                  continue;
              fi;
              v := v / v[w.n];   # normalize to 1 in position n
              Assert(1,v*c=v);
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
          RECOG.CopySubVectorCompat(zerovec,newpart[i],[1..w.n],[1..w.n]);
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
          if Dimension(int3) <> w.d-2*w.n+1 then
              Info(InfoRecog,2,"Ooops, FixSLn \cap Fixc wrong dimension");
              continue;
          fi;
          Append(newbas,BasisVectors(Basis(int3)));
      fi;
      ConvertToMatrixRep(newbas,w.f);
      newbasi := newbas^-1;
      if newbasi = fail then
          Info(InfoRecog,2,"Ooops, Fixc intersected too much, we try again");
          continue;
      fi;
      ci := newbas * ci * newbasi;
      cii := ExtractSubMatrix(ci,[w.n+1..aimdim],[1..w.n-1]);
      ConvertToMatrixRep(cii,w.f);
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
      Info(InfoRecog,2,"Ooops, no nice bottom...");
      # Otherwise simply try again
  od;
  Info(InfoRecog,2," found c1 and c.");
  # Now SL_n has to be repaired according to the base change newbas:

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
              tf := DoRowOp_n(tf,j,w.n,-ci[j,i]*lambda,w);
          od;
          Add(trans,tf);
      od;
  od;

  # Now put together the clean ones by our knowledge of c^-1:
  transd := [];
  for i in [1..Length(pivots2)] do
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
          tf := DoRowOp_n(tf,j,w.n,-ci[j,w.n],w);
      od;
      # Now cleanup in rows below row n:
      for j in [1..newdim] do
          coeffs := IntVecFFE(Coefficients(w.can,-ci[w.n+j,w.n]));
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
          tf := DoColOp_n(tf,j,w.n,ci[j,w.n],w);
      od;
      # Now cleanup row n left of column n:
      for j in [1..w.n-1] do
          tf := DoRowOp_n(tf,w.n,j,-c[i,j],w);
      od;
      # Now cleanup column n below row n:
      for j in [1..newdim] do
          coeffs := IntVecFFE(Coefficients(w.can,ci[w.n+j,w.n]));
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
  ConvertToMatrixRep(mat,w.f);
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
