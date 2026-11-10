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
##  FinalDescent for special linear groups
##
#############################################################################

#g=SL(d,q), given as a subgroup of SL(dim,q)
#output: [SL(2,q), and a basis for the 2-dimensional subspace where it acts
RECOG.SLn_godownfromd:=function(g,q,d,dim)
  local y,yy,ready,order,es,dims,subsp,z,x,a,b,c,h,vec,vec2,
  pol,factors,degrees,comm1,comm2,comm3,image,basis,action,vs,readyqpl1,
  readyqm1,count,u,orderu,expecteddims;

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
            # Since yy^(q-1)=1, yy is semisimple over GF(q).  We want
            # one 1-space, one (d-1)-space, and the fixed outside space
            # of dimension dim-d; the last one is absent when dim=d.
            expecteddims:=Filtered([1,d-1,dim-d], x -> x > 0);
            if AsSortedList(dims)=AsSortedList(expecteddims) then
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

# FinalDescent of [EHNPR] for SL: <gens> generate SL(4,q), q = Size(<f>).
# Returns rec(slp := SLP in <gens> for the standard generators of an
# SL(2,q), bas := a 4x4 matrix whose first two rows span the space on which
# it acts and whose last two span its fixed space) such that relative to
# bas the standard generators are those of RECOG.MakeSL_StdGens(p,ext,2,4).
RECOG.SLn_FinalDescent := function(gens, f)
  local q, p, ext, std, h, sl2, sl2gens, V, fix, b, action, resl2, slp;

  q := Size(f);
  p := Characteristic(f);
  ext := DegreeOverPrimeField(f);

  # SLn_godownfromd does not apply to these fields; constructive
  # membership in SL(4,q) yields the SL(2,q) instead
  if q in [2,3,4,5,9] then
    Info(InfoRecog_ClassicalNatural,1,"SL_n: base case SL(4,",q,")");
    std := RECOG.MakeSL_StdGens(p,ext,2,4).all;
    return rec( slp := RECOG.FindStdGensUsingBSGS(Group(gens),std,false,false),
                bas := IdentityMat(4,f) );
  fi;

  Info(InfoRecog_ClassicalNatural,1,"SL_n: base case SL(2,",q,")");
  h := GroupWithMemory(gens);
  sl2 := RECOG.SLn_godownfromd(h,q,4,4);
  sl2gens := GeneratorsOfGroup(sl2[1]);
  V := BasisVectors(Basis(sl2[2]));
  fix := BasisVectors(Basis(Intersection(List(StripMemory(sl2gens),
             x -> VectorSpace(f, RECOG.FixspaceMat(x))))));
  Assert(1, Length(fix) = 2 and RankMat(Concatenation(V, fix)) = 4);

  b := Basis(sl2[2],V);
  action := List(StripMemory(sl2gens),x->RECOG.LinearAction(b,f,x));
  resl2 := RECOG.RecogniseSL2Natural(Group(GeneratorsWithMemory(action)),f);
  slp := CompositionOfStraightLinePrograms(SLPOfElms(resl2.all),
                                           SLPOfElms(sl2gens));
  b := Concatenation(resl2.bas * V, fix);
  ConvertToMatrixRep(b,f);
  return rec( slp := slp, bas := b );
end;
