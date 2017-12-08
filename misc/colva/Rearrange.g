MyIsInnerAutomorphism := function(grp,name,phi,membershiptest)
# Is phi an inner automorphism (possibly modulo scalars) of the quasisimple matrix group grp or direct product of quasisimple groups of given names?
# membership test is a membership test in grp
 local m,g,gens,ims1,oz,o,z,ims,F,M1,M2,mat,t,i,detmat,z1,j,d
       ,el,t1,k,names,celt,gp,mtest,kappa,bool;


# Have to deal with each direct product component seperately
 names := SplitString(name,",");
 celt := One(grp);

 for k in [1..Length(names)] do
   if IsDirectProduct(grp) then
     gp := Image(MyProjection(grp,k));
     kappa := GroupHomomorphismByFunction(gp,gp,g->
ImageElm(MyProjection(grp,k),ImageElm(phi,ImageElm(MyEmbedding(grp,k),g))));
     #I'm pretty sure that the following is safe....
     SetIsBijective(kappa, true);
     mtest := g->membershiptest(ImageElm(MyEmbedding(grp,k),g));
   else
     gp := grp;
     kappa := phi;
     mtest := membershiptest;
   fi;

  #was falling over with socle factor A_5s cos they became perm grps,
  #hopefully this will catch it.
  if IsPermGroup(gp) then
    bool:= IsInnerAutomorphism(kappa);
    if not bool then
      return false;
    elif not IsDirectProduct(grp) then
      return ConjugatorOfConjugatorIsomorphism(kappa);
    else
      celt:= celt*ImageElm(MyEmbedding(grp, k), ConjugatorOfConjugatorIsomorphism(kappa));
      break;
    fi;
  fi;

# First construct a generating set of elts of order coprime to the schur multiplier
   m := SchurMultiplierOrder(names[k]);
   g := ElementOfCoprimeOrder(gp,m);
# Compute a number of random conjugates of g to get a probable generating set for gp

   gens := Concatenation([g],List([1..5],i->g^PseudoRandom(gp)));

# compute the images of gens under phi
   ims1 := List(gens,x->ImageElm(kappa,x));

# alter images to remove the scalar parts
   oz := List(ims1,x->ProjectiveOrder(x));
   o := List(oz,x->x[1]);
   z := List(oz,x->x[2]);
   m := List([1..Size(z)],i->-1/o[i] mod Order(z[i]));
   ims := List([1..Size(z)],i->ims1[i]*z[i]^m[i]);


# Do we have module isomorphisms?

   F := FieldOfMatrixGroup(gp);
   M1 := GModuleByMats(gens,F);
   M2 := GModuleByMats(ims,F);

   mat := MTX.IsomorphismModules(M1,M2);
   if not IsMatrix(mat) then return false; fi;



# So we have some scalar matrix z with z*mat in grp?
   z := PrimitiveElement(F);

   d := DimensionOfMatrixGroup(gp);
# This should be included when LogFFE stops returning an error if # there is no solution

   detmat := Determinant(mat);
   j := LogFFE(detmat^-1,z^d);
   if j = fail then return false; fi;
   z1 := z^(GcdInt(Size(F)-1,d));

#   for i in [0..Order(z)-1] do
   for i in [0..Order(z1)-1] do
     t := (z1^i*z^j)*One(gp)*mat;
#     t := (z^i)*One(gp)*mat;
     if IsStraightLineProgram(mtest(t)) then
       if IsDirectProduct(grp) then
         celt := celt * ImageElm(MyEmbedding(grp,k),t);
         break;
       else
         return t;
       fi;
     fi;
     if i = Order(z1)-1 then return false; fi;
   od;
 od;
 return celt;
end;

# Can we push past a nonabelian layer? generally used to try to push past the socle.
PastNonAb := function(ri)
 local x,riker,aut,w,preim,t,inns,i,innspreims,y,l,rihom,kerhom
       ,zeta, conj_elt;


 x := pregensfac(ri)[1];
 if IsDirectProduct(Grp(RIFac(RIKer(ri)))) and not IsTrivial(PermAction(GroupWithGenerators([x]),Grp(RIKer(ri)),Homom(RIKer(ri)),Grp(RIFac(RIKer(ri))))) then return false;
 fi;

 riker := RIKer(ri);
# Consider the automorphism of RIFac(riker) induced by x
 aut := GroupHomomorphismByFunction(Grp(RIFac(riker)),Grp(RIFac(riker)),
function(g)
 local w,preim;
 w := slpforelement(RIFac(riker))(RIFac(riker),g);
 preim := ResultOfStraightLineProgram(w,pregensfac(riker));
 return ImageElm(Homom(riker),preim^x);
end);
# Is aut inner? - tell it that it's an automorphism.
 SetIsBijective(aut, true);
 t := MyIsInnerAutomorphism(Grp(RIFac(riker)),Name(RIFac(riker)),aut,g->slpforelement(RIFac(riker))(RIFac(riker),g));
 if t=false then return false; fi;

# Check that all automorphisms induced by prefacgens induce inner auto's
 inns := [t];
 for i in [2..Length(pregensfac(ri))] do
   x := pregensfac(ri)[i];
   aut := GroupHomomorphismByFunction(Grp(RIFac(riker)),Grp(RIFac(riker)),
function(g)
 local w,preim;
 w := slpforelement(RIFac(riker))(RIFac(riker),g);
 preim := ResultOfStraightLineProgram(w,pregensfac(riker));
 return ImageElm(Homom(riker),preim^x);
end);
   conj_elt:= MyIsInnerAutomorphism(Grp(RIFac(riker)),Name(RIFac(riker)),aut,g->slpforelement(RIFac(riker))(RIFac(riker),g));
   if conj_elt = false then return false; fi;
   Add(inns, conj_elt);
 od;


 innspreims := List(inns, t->ResultOfStraightLineProgram(slpforelement(RIFac(riker))(RIFac(riker),t),pregensfac(riker)));

# Construct a lifting into the centraliser
 y := List([1..Length(innspreims)],i->pregensfac(ri)[i]*innspreims[i]^-1);
# Define a lifting -
 l := x->ResultOfStraightLineProgram(slpforelement(RIFac(ri))(RIFac(ri),x),y);


 rihom := StructuralCopy(Homom(ri));
 kerhom := StructuralCopy(Homom(riker));
 zeta := GroupHomomorphismByFunction(Grp(ri),Grp(RIFac(riker)),function(g)
 local g1;
 g1 := l(ImageElm(rihom,g));
 return ImageElm(kerhom,g*g1^-1);
 end);

 return zeta;
end;

#returns a function from Grp(ri) to Grp(RIFac(RIKer(ri))) if can do so,
#otherwise returns false.
AbPastAb := function(ri)
## Tries to push an abelian layer past another abelian layer where the layers are over different primes
 local x,riker,i,im,q,l,zeta;

 x := pregensfac(ri)[1];
 riker := RIKer(ri);;
# Does x act trivially on RIFac(riker)
 for i in [1..Length(NiceGens(RIFac(riker)))] do
   im := ImageElm(Homom(riker),pregensfac(riker)[i]^x);
   if im <> NiceGens(RIFac(riker))[i] then
     return false;
   fi;
 od;

# Now we know x acts trivially on RIFac(riker)
# Construct the new lifting
 q := Grp(RIFac(riker))!.Pcgs!.RelativeOrders[1];
 l := GroupHomomorphismByImagesNC(Grp(RIFac(ri)),Grp(ri),List(NiceGens(RIFac(ri)),x->x^q),List(pregensfac(ri),x->x^q));

# Construct the new map
 zeta := GroupHomomorphismByFunction(Grp(ri),Grp(RIFac(riker)),g->ImageElm(Homom(riker),g*ImageElm(Homom(ri)*l,g)^-1));
 return zeta;
end;


AbPastAbSamePrime := function(ri)
## Tries to push an abelian layer past another abelian layer where the layers are over the same prime. returns a list of homs in this case
 local x,riker,i,im,p,l,psi,checkelts1,checkelts2,D,phi,pregens,
       g,M,CS,maps,zeta,k,AcGens,L,intorikerfac;

 x := pregensfac(ri)[1];
 riker := RIKer(ri);;
 if not SanityCheck(ri) then
   Error(179);
 fi;
# Does x act trivially on RIFac(riker)
 for i in [1..Length(NiceGens(RIFac(riker)))] do
   im := ImageElm(Homom(riker),pregensfac(riker)[i]^x);
   if im <> NiceGens(RIFac(riker))[i] then
     return [false];
   fi;
 od;

# Construct a map down onto the direct product of the two factor groups
 p := Grp(RIFac(riker))!.Pcgs!.RelativeOrders[1];
 l := GroupHomomorphismByImagesNC(Grp(RIFac(ri)),Grp(ri),NiceGens(RIFac(ri)),pregensfac(ri));
 psi := GroupHomomorphismByFunction(Grp(ri),Grp(RIFac(riker)),g->ImageElm(Homom(riker),g*ImageElm(l,ImageElm(Homom(ri),g))^-1));
# check generators and relations of facto(ri) map to 1 under psi
 checkelts1 := List(pregensfac(ri),x->x^p);
 if not ForAll(checkelts1,x->IsOne(ImageElm(psi,x))) then return [false]; fi;
 checkelts2 := Concatenation(List([1..Length(pregensfac(ri))],i->List([(i+1)..Length(pregensfac(ri))],j->Comm(pregensfac(ri)[i],pregensfac(ri)[j]))));
 if not ForAll(checkelts2,x->IsOne(ImageElm(psi,x))) then return [false]; fi;

 D := DirectProduct(Grp(RIFac(ri)),Grp(RIFac(riker)));
 phi := GroupHomomorphismByFunction(Grp(ri),D,g->ImageElm(Homom(ri)*Embedding(D,1),g)*ImageElm(psi*Embedding(D,2),g));
 pregens := Concatenation(pregensfac(ri),pregensfac(riker));
# Construct the action of G on D
 AcGens := [];
 for g in GeneratorsOfGroup(overgroup(ri)) do
   Add(AcGens,List(pregens,x->ExponentsOfPcElement(Pcgs(D),ImageElm(phi,x^g))));
 od;
# Construct the minimal submodules of the module
 M := GModuleByMats(Z(p)^0*AcGens,GF(p));
 CS := MTX.BasesMinimalSubmodules(M);

# get the list of normal subgroups

 L := List(CS,x->
SubgroupNC(D,List(x,v->VectortoPc(v,D))));
 for i in [1..Length(L)] do
   if L[i]=Image(MyEmbedding(D,2)) then Remove(L,i); break; fi;
 od;
 if Length(L)=0 then return [false]; fi;


 maps := List(L,x->NaturalHomomorphismByNormalSubgroupNC(D,x));
 intorikerfac := List(maps,x->IsomorphismGroups(Range(x),Grp(RIFac(riker))));


 zeta := List([1..Length(L)],i->GroupHomomorphismByFunction(Grp(ri),Grp(RIFac(riker)),g->ImageElm(intorikerfac[i],ImageElm(maps[i],ImageElm(phi,g)))));
 return zeta;
end;

NonAbPastAb := function(ri)
## Tries to push a non abelian layer past an abelian layer. This algorithm is randomized due to the lack of presentations.
## Only works if the nonabelian layer is a perm group
 local x,riker,i,target_size,s,im,gens,g,p,words,invims,invims1,gens2,
    zeta,h,lift,g1;

 if not IsPermGroup(Grp(RIFac(ri))) then return false; fi;
 x := pregensfac(ri)[1];
 riker := RIKer(ri);;
# Does x act trivially on RIFac(riker)
 for i in [1..Length(NiceGens(RIFac(riker)))] do
   im := ImageElm(Homom(riker),pregensfac(riker)[i]^x);
   if im <> NiceGens(RIFac(riker))[i] then
     return false;
   fi;
 od;

# construct a new generating set of elts coprime to p

  p := Grp(RIFac(riker))!.Pcgs!.RelativeOrders[1];
  target_size:= Size(RIFac(ri));
  gens := [];
  #first see if just 4 generators will suffice
  for i in [1..4] do
    repeat
      g := PseudoRandom(Grp(RIFac(ri)));
      g := g^(p^Valuation(Order(g),p));
    until not IsOne(g);
    Add(gens,g);
  od;
  #this contains known upper limit target_size for Group(gens);
  s:= StabChain(GroupWithGenerators(gens), rec(random:= 1,
                                        limit:= target_size));
  #if haven't yet found enough, add extra generators
  #one-by-one and check each time.
  while SizeStabChain(s) < target_size do
    repeat
      g := PseudoRandom(Grp(RIFac(ri)));
      g := g^(p^Valuation(Order(g),p));
    until not IsOne(g);
    Add(gens, g);
    s:= StabChain(GroupWithGenerators(gens), rec(random:= 1,
                limit:= target_size));
  od;

 #all of these were PseudoRandom(Grp(ri)) but since that's a matrix
 #group i presume should be conjugating in RIFac(ri) - Colva.
 #Add(gens,g^PseudoRandom(Grp(RIFac(ri))));
 #Add(gens,g^PseudoRandom(Grp(RIFac(ri))));
 #Add(gens,g^PseudoRandom(Grp(RIFac(ri))));
 #repeat
 #  g := PseudoRandom(Grp(RIFac(ri)));
 #  g := g^(p^Valuation(Order(g),p));
 #until not IsOne(g);
 #Add(gens,g);
 #Add(gens,g^PseudoRandom(Grp(RIFac(ri))));
 #Add(gens,g^PseudoRandom(Grp(RIFac(ri))));
 #Add(gens,g^PseudoRandom(Grp(RIFac(ri))));

 words := List(gens,x->SLPforElement(RIFac(ri),x));
 invims1 := List(words,w->ResultOfStraightLineProgram(w,pregensfac(ri)));
 invims := List(invims1,x->x^(p^Valuation(Order(x),p)));
 #should this be invims1 or invims in next line???
 gens2 := List(invims, x->ImageElm(Homom(ri),x));
 lift := GroupHomomorphismByImagesNC(Grp(RIFac(ri)),Grp(ri),gens2,invims);
 zeta := GroupHomomorphismByFunction(Grp(ri),Grp(RIFac(riker)),g->ImageElm(Homom(riker),g*ImageElm(lift, ImageElm(Homom(ri),g))^-1));


# Do some random testing of elts to check that zeta is a hom
 for i in [1..20] do
   g := PseudoRandom(Grp(ri));
   g1:= ImageElm(zeta, g);
   h := PseudoRandom(Grp(ri));
   if g1*ImageElm(zeta,h)<>ImageElm(zeta,g*h) then
     return false;
   fi;
 od;
 return zeta;
end;


PushIntoSocle := function(ri,zeta)
# ri is the layer of the tree just above the socle. riker maps into the socle and zeta is a map from Grp(ri) ino the socle
 local riker,D,phi,im1,im2,nri,nrifac,list,g,overgp;


 riker := RIKer(ri);;
# Form the direct product of the socle
 D := DirectProduct(Grp(RIFac(ri)),Grp(RIFac(riker)));
# and the new map phi from Grp(ri) -> D
 phi := GroupHomomorphismByFunction(Grp(ri),D,function(g)
local im1,im2;
im1 := ImageElm(Homom(ri),g);
im2 := ImageElm(zeta,g);
return ImageElm(MyEmbedding(D,1),im1)*ImageElm(MyEmbedding(D,2),im2);
end);


 overgp := ShallowCopy(overgroup(ri));

# setup the new record for the factor - this is the product of RIFac(ri) and RIFac(riker)
 nrifac := rec();
 Objectify( RecognitionInfoType, nrifac );;

#new factor group is direct product of old factor groups, both are now in the socle.
 SetGrp(nrifac,D);

#map the NiceGens for each factor into the direct product, and take both sets of NiceGens.
 SetNiceGens(nrifac,Concatenation(List(NiceGens(RIFac(ri)),x->ImageElm(MyEmbedding(D,1),x)),List(NiceGens(RIFac(riker)),x->ImageElm(MyEmbedding(D,2),x))));

 SetFilterObj(nrifac,IsLeaf);
 Setfhmethsel(nrifac,"socle");
 Setslpforelement(nrifac, function(nrifac,g)

   local list;
   list := [SLPforElement(RIFac(ri),ImageElm(MyProjection(D,1),g)),SLPforElement(RIFac(riker),ImageElm(MyProjection(D,2),g))];
   if fail in list then return fail; fi;
   return MyDirectProductOfSLPsList(list);
 end
 );
 SetSize(nrifac,Size(RIFac(ri))*Size(RIFac(riker)));
 SetFilterObj(nrifac,IsReady);

# setup the new record for the subgroup - nri will take the place of the old ri, but iwth
#ker(riker) as its kernel and nrifac, the new socle, as its factor.
 nri := rec();
 Objectify( RecognitionInfoType, nri );;
 SetRIFac(nri,nrifac);
 SetGrp(nri,Grp(ri));
 if HasRIParent(ri) then
   SetRIParent(nri,RIParent(ri));
   SetRIKer(RIParent(nri),nri);
   if not SanityCheck(RIParent(nri)) then
     Error(1);
   fi;
 fi;
 if HasRIKer(riker) and RIKer(riker) = fail then
   SetRIKer(nri, fail);
 elif HasRIKer(riker) then
   SetRIKer(nri,RIKer(riker));
   SetRIParent(RIKer(nri),nri);
   if not SanityCheck(nri) then
     Error(2);
   fi;
 fi;
 SetHomom(nri,phi);
## Construct the preimages
 Setpregensfac(nri,Concatenation(
List(pregensfac(ri),g->
g*ResultOfStraightLineProgram(SLPforElement(RIFac(riker),ImageElm(phi*MyProjection(D,2),g)),pregensfac(riker))^-1),
pregensfac(riker)));
 #this was causing problems with the kernel was fail.
 if HasRIKer(nri) and RIKer(nri) <> fail then
   SetNiceGens(nri,Concatenation(pregensfac(nri),NiceGens(RIKer(nri))));
 elif HasRIKer(nri) then
 #so the kernel is the trivial group, just need preimages of the socle generators.
   SetNiceGens(nri, pregensfac(nri));
 fi;
 Setcalcnicegens(nri,CalcNiceGensHomNode);
 SetName(nrifac,Concatenation(Name(RIFac(ri)),",",Name(RIFac(riker))));
 Setslpforelement(nri,SLPforElementGeneric);
 Setovergroup(nri,overgp);
 SetFilterObj(nri,IsReady);
 if not SanityCheck(nri) then
   Error(10001);
 fi;
 return nri;
end;


#this function is used for all position swaps other than pushing a factor
#into the socle.
SwapFactors := function(ri,zeta)
# Swaps the layers of the tree at ri using the map
# zeta : Grp(ri) -> Grp(RIFac(RIKer(ri)))


 local riker,rifac,rikerfac,nri,nriker,overgp;

 riker := RIKer(ri);;
 rifac := RIFac(ri);;
 rikerfac := RIFac(riker);;

# setup the new record for the factor
 nri := rec();
 Objectify( RecognitionInfoType, nri );;
 nriker := rec();
 Objectify( RecognitionInfoType, nriker );;

 SetHomom(nriker,StructuralCopy(Homom(ri)));
 SetHomom(nri,zeta);
 Setpregensfac(nri,StructuralCopy(pregensfac(riker)));
 Setpregensfac(nriker,List(pregensfac(ri),x->x*ResultOfStraightLineProgram(SLPforElement(rikerfac,ImageElm(zeta,x)),pregensfac(riker))^-1));
 SetRIKer(nriker,StructuralCopy(RIKer(riker)));
 SetRIParent(RIKer(nriker),nriker);
 SetRIParent(nriker,nri);
 SetRIKer(nri, nriker);
 if not SanityCheck(nri) then
   Error(3);
 fi;
 SetRIFac(nriker,StructuralCopy(RIFac(ri)));
 #next two lines had capital p for parent before.
 #if IsBound(ri!.RIParent) then not sure whether should be checking HasRIParent, try that instead.
 if HasRIParent(ri) then
   SetRIParent(nri,StructuralCopy(RIParent(ri)));
   SetRIKer(RIParent(nri),nri);
   if not SanityCheck(RIParent(nri)) then
     Error(4);
   fi;
 fi;
 if HasRIKer(riker) then
   SetRIKer(nriker,RIKer(riker));
   SetRIParent(RIKer(riker),nriker);
   if not SanityCheck(nri) then
     Error(5);
   fi;
 fi;
 SetRIFac(nri,StructuralCopy(RIFac(riker)));
 #value of NiceGens is either the ones of the image on their own if kernel
 #is trivial, or gens for image plus gens for kernel.
 if HasRIKer(nriker) and not (RIKer(nriker) = fail) then
   SetNiceGens(nriker,Concatenation(pregensfac(nriker),NiceGens(RIKer(nriker))));
 else
   SetNiceGens(nriker, pregensfac(nriker));
 fi;
 SetNiceGens(nri,Concatenation(pregensfac(nri),NiceGens(nriker)));
 Setcalcnicegens(nri,CalcNiceGensHomNode);
 Setcalcnicegens(nriker,CalcNiceGensHomNode);
 SetGrp(nri,StructuralCopy(Grp(ri)));
 #the group of nriker is the generators of the group of its kernel(if nontrivial) plus the preimages of the factor.
 if HasRIKer(nriker) and not RIKer(nriker) = fail then
   SetGrp(nriker,GroupWithGenerators(Concatenation(GeneratorsOfGroup(Grp(RIKer(nriker))),pregensfac(nriker))));
 elif HasRIKer(nriker) then
   SetGrp(nriker,GroupWithGenerators(pregensfac(nriker)));
 fi;
 Setslpforelement(nri,SLPforElementGeneric);
 Setslpforelement(nriker,SLPforElementGeneric);
 overgp := ShallowCopy(overgroup(ri));
 Setovergroup(nri,overgp);
 Setovergroup(nriker,overgp);
 SetFilterObj(nri,IsReady);
 SetFilterObj(nriker,IsReady);
 if not SanityCheck(nri) then
   Error(79);
 fi;
 return nri;
end;


#this checks that every factor group in the chief tree is polycyclic, if
#so then group is soluble.
IsSolubleTree := function(ri)
 if not IsBound(Grp(RIFac(ri))!.Pcgs) then return false; fi;
 if ri!.RIKer <> fail then return IsSolubleTree(RIKer(ri));
 else
   return true;
 fi;
end;


#this is the main function for the rearrangement. We have three nodes, namely pri,
#priker and ker(priker) with corresponding factor groups prifac and prikerfac, and are trying
#to either put prifac and prikerfac on the same level (if they are both nonabelian simple and #hence part of the socle), or push prifac past prikerfac.

PushDown := function(pri)
 local priker,prifac,prikerfac,zeta,i,npri,nnpri,knpri;

 priker := RIKer(pri);
 prifac := RIFac(pri);
 prikerfac := RIFac(priker);

# Compute the push down maps - they depend on which groups are abelian.

 if not IsBound(Grp(prikerfac)!.Pcgs) then
# prikerfac is nonabelian
   Print("Calling PastNonAb(pri)\n");
   zeta := [PastNonAb(pri)];

 elif not IsBound(Grp(prifac)!.Pcgs) then
# prikerfac is abelian and priker is nonabelian
   Print("Calling NonAbPastAb(pri)\n");
   zeta := [NonAbPastAb(pri)];

 elif Grp(prifac)!.Pcgs!.RelativeOrders[1] = Grp(prikerfac)!.Pcgs!.RelativeOrders[1] then
# prifac and prikerfac are abelian over the same prime, this function returns a list of maps.
  Print("doing AbPastAbSamePrime\n");
  zeta := AbPastAbSamePrime(pri);

 else
#both groups are abelian over different primes.
  Print("Calling AbPastAb");
   zeta := [AbPastAb(pri)];
 fi;

 if zeta = [false] then
   Print("zeta was false, record is now\n");
   View(pri);
   return false;
 fi;

# Is RIFac(priker)) the socle, i.e. are we pushing down into or
#past the socle?
 if IsBound(prikerfac!.TFordered) and prikerfac!.TFordered="Socle" then
   zeta := zeta[1];
 #if both groups are insoluble then they should both be in the socle together.
   if not IsBound(Grp(prifac)!.Pcgs) then
     npri := PushIntoSocle(pri,zeta);;
     SetTFordered(RIFac(npri),"Socle");
   else
 #otherwise we should put prifac below prikerfac.
     npri := SwapFactors(pri,zeta);;
   fi;
   View(npri);
   if not SanityCheck(RIParent(npri)) then
     Error(101);
   fi;
   return npri;
 fi;

#this is the case where RIFac(priker) is not the socle, we try
#each of our maps in turn and
#look to see whether we can push pri down a level, then recurse to
#try to push it down further.
#successful recursion terminates once we've pushed it down past or
#into the socle - the previous paragraph of this code. if we can't
#do that then there's no point moving it at all.
 for i in [1..Length(zeta)] do
   Print("trying zeta, i is", i, "\n");
   npri := SwapFactors(StructuralCopy(pri),zeta[i]);;
   knpri := PushDown(StructuralCopy(RIKer(npri)));;
#having a problem with something believing it's got a parent when it doesn't.
   if knpri <> false and npri <> false then
#found a map that works.
     SetRIKer(npri,knpri);
     SetRIParent(knpri,npri);
     if not SanityCheck(npri) then
       Error(6);
     fi;
     SetNiceGens(npri,Concatenation(pregensfac(npri),NiceGens(knpri)));
     View(npri);
     if not SanityCheck(npri) then
       Error(7);
     fi;
     return npri;
   fi;
 od;
 return false;
end;




OrderTree := function(ri)
# Order the tree as in the TF model
 local lastnonabri,pri,npri;

  ri:= StructuralCopy(ri);
# Is the tree soluble? in that case all is O_{\infty}(G) already.
 if IsSolubleTree(ri) then return ri; fi;
# Is G simple?
 if ((not HasRIKer(ri)) or (RIKer(ri) = fail)) then return ri; fi;

# Find the last non-abelian chief factor.
 lastnonabri := StructuralCopy(ri);
 while RIKer(lastnonabri) <> fail and not IsSolubleTree(RIKer(lastnonabri)) do
   lastnonabri := RIKer(lastnonabri);
 od;

# Tell that chief factor that it will be where the socle collects.
 SetTFordered(RIFac(lastnonabri),"Socle");


# Go to socle layer.
 pri:= StructuralCopy(lastnonabri);

# Push the soluble layers down
 while HasRIParent(pri) do
   pri := StructuralCopy(RIParent(pri));
   SetNiceGens(pri,Concatenation(pregensfac(pri),NiceGens(RIKer(pri))));
   npri := PushDown(StructuralCopy(pri));;
   if npri <> false then
     pri := StructuralCopy(npri);
     if not SanityCheck(pri) then
       Error(75);
     fi;
   fi;
 od;

 #this is kind of messy, but i haven't managed to track down where all the
 #parent kernel factor not matching up errors are occurring
 while HasRIKer(pri) and not RIKer(pri) = fail do
   SetRIParent(RIKer(pri), pri);
   SetRIParent(RIFac(pri), pri);
   pri:= RIKer(pri);
 od;
 while HasRIParent(pri) do
   pri:= RIParent(pri);
 od;
 return pri;
end;

