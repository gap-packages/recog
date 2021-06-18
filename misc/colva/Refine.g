SolvePcWord := function(rri,g)
 local T,PtoT;
 T := GroupWithMemory(GroupWithGenerators(List(AsList(Pcgs(Grp(rri))),x->())));
 PtoT := GroupHomomorphismByImages(Grp(rri),T,AsList(Pcgs(Grp(rri))),GeneratorsOfGroup(T));

 return SLPOfElm(ImageElm(PtoT,g));
end;




InsertSubTree := function(ri,rifac,maps)
# insert a subtree in ri where maps is a sequence of normal series maps for Grp(rifacs)
 local kerfac,phi,Q,GtoQ,lri,rri,ripregensfac,overgp,i,kgens;

 # remember the kernel of ri!
 kerfac := KernelRecogNode(ri);;

 # construct maps from ri -> new groups
 phi := StructuralCopy(Homom(ri));
 Q := List(maps,x->Image(x));
 GtoQ := List([1..Length(Q)],i->GroupHomomorphismByFunction(Grp(ri),Q[i],g->ImageElm(maps[i],ImageElm(phi,g))));


 lri := []; rri := [];
 lri[1] := rec();
 Objectify(RecognitionInfoType,lri[1]);;

 SetGrp(lri[1],Grp(ri));

 ripregensfac := ShallowCopy(PreImagesOfNiceGeneratorsOfImageNode(ri));
 overgp := ShallowCopy(overgroup(ri));
 Setovergroup(lri[1],overgp);

 for i in [1..Length(Q)] do
   rri[i] := rec();
   Objectify(RecognitionInfoType,rri[i]);;
   SetGrp(rri[i],Q[i]);
   SetHomom(lri[i],GtoQ[i]);
   SetNiceGenerators(rri[i],AsList(Pcgs(Q[i])));
   Setslpforelement(rri[i],SolvePcWord);
   SetPreImagesOfNiceGeneratorsOfImageNode(lri[i],List(NiceGenerators(rri[i]),x-> ResultOfStraightLineProgram(slpforelement(rifac)(rifac,PreImagesRepresentative(maps[i],x)),ripregensfac)));
   SetRECOG_CalcNiceGeneratorsFunctionOfRecogNode(lri[i],CalcNiceGeneratorsForSplitNode);
   lri[i]!.nrgensH := Length(GeneratorsOfGroup(Grp(lri[i])));
   Setovergroup(lri[i],overgp);
   SetRECOG_CalcNiceGeneratorsFunctionOfRecogNode(lri[i],CalcNiceGeneratorsForLeafNode);
   Setslpforelement(lri[i],SLPforElementGeneric);
   SetFilterObj(rri[i],IsLeaf);
   SetFilterObj(rri[i],IsReady);
   SetFilterObj(lri[i],IsReady);

   lri[i]!.genswithmem := GeneratorsWithMemory(
            Concatenation(GeneratorsOfGroup(Grp(lri[i])),PreImagesOfNiceGeneratorsOfImageNode(lri[i])));
   lri[i]!.groupmem := Group(lri[i]!.genswithmem{[1..lri[i]!.nrgensH]});
   # FIXME: This is broken due to the new random element infrastructure!


# Setup the kernel

   if kerfac <> fail then
     kgens := Concatenation(GeneratorsOfGroup(Grp(kerfac)),List(GeneratorsOfGroup(Kernel(maps[i])),x->ResultOfStraightLineProgram(slpforelement(rifac)(rifac,x),ripregensfac)));
   else
     kgens := List(GeneratorsOfGroup(Kernel(maps[i])),x->ResultOfStraightLineProgram(slpforelement(rifac)(rifac,x),ripregensfac));
   fi;
   if Length(kgens)=0 then
     kgens := [One(overgp)];
   fi;
   lri[i+1] := rec();
   Objectify(RecognitionInfoType,lri[i+1]);;
   SetGrp(lri[i+1],GroupWithGenerators(kgens));
   SetKernelRecogNode(lri[i],lri[i+1]);
   SetImageRecogNode(lri[i],rri[i]);
   SetParentRecogNode(lri[i+1],lri[i]);
   SetParentRecogNode(rri[i],lri[i]);
 od;


 # tell lri[1] to join onto ParentRecogNode(ri)
 if HasParentRecogNode(ri) then
   SetParentRecogNode(lri[1],StructuralCopy(ParentRecogNode(ri)));
 fi;

 # tell last lri to be kerfac
   SetKernelRecogNode(lri[Size(Q)],StructuralCopy(kerfac));
   SetParentRecogNode(KernelRecogNode(lri[Size(Q)]),lri[Size(Q)]);

 # Set up the nice generators

 i := Size(Q);
 while i>0 do
   if KernelRecogNode(lri[i]) <> fail then
     SetNiceGenerators(lri[i],Concatenation(PreImagesOfNiceGeneratorsOfImageNode(lri[i]),NiceGenerators(KernelRecogNode(lri[i]))));
   else
     SetNiceGenerators(lri[i],PreImagesOfNiceGeneratorsOfImageNode(lri[i]));
   fi;
   i := i - 1;
 od;

 return lri[1];
end;


RefineSolubleLayers := function(ri)
 local rifac,phi,I,L,maps,riker;

 if ri=fail then return ri; fi;

 rifac := ImageRecogNode(ri);;
 phi := Homom(ri);
 I := Grp(rifac);

 if not IsPcGroup(I) or IsElementaryAbelian(I) then
   riker := KernelRecogNode(ri);
   SetKernelRecogNode(ri,RefineSolubleLayers(riker));
   if KernelRecogNode(ri)<>fail then
     SetNiceGenerators(ri,Concatenation(PreImagesOfNiceGeneratorsOfImageNode(ri),NiceGenerators(KernelRecogNode(ri))));
   else
     SetNiceGenerators(ri,PreImagesOfNiceGeneratorsOfImageNode(ri));
   fi;
   return ri;
 fi;

  L := InvariantElementaryAbelianSeries(I,GeneratorsOfGroup(AutomorphismGroup(I)) : fine := true);
  maps := List([1..Length(L)-1],i->NaturalHomomorphismByNormalSubgroupNC(L[i],L[i+1]));
  ri := InsertSubTree(ri, rifac, maps);;
  riker := KernelRecogNode(ri);
  SetKernelRecogNode(ri,RefineSolubleLayers(riker));
  SetParentRecogNode(KernelRecogNode(ri),ri);
  if KernelRecogNode(ri)<>fail then
    SetNiceGenerators(ri,Concatenation(PreImagesOfNiceGeneratorsOfImageNode(ri),NiceGenerators(KernelRecogNode(ri))));
  else
    SetNiceGenerators(ri,PreImagesOfNiceGeneratorsOfImageNode(ri));
  fi;

  return ri;
end;


ConstructActionMatrices := function(ri)
# Constructs the action matrices of the overgroup on the elementary abelian layer
 local AcGens,x,g;

 AcGens := [];
 for g in GeneratorsOfGroup(overgroup(ri)) do
   Add(AcGens,List(PreImagesOfNiceGeneratorsOfImageNode(ri),x->ExponentsOfPcElement(Pcgs(ImageRecogNode(ri)!.group),ImageElm(Homom(ri),x^g))));
 od;

 return AcGens;
end;

VectortoPc := function(v,Pc)
 return PcElementByExponents(Pcgs(Pc),List(v,x->IntFFE(x)));
end;

RefineElementaryAbelianLayers := function(ri)
 local rifac,phi,I,L,maps,riker,AcGens,CS,p,M,v;

 if ri=fail then return ri; fi;

 rifac := ImageRecogNode(ri);;
 phi := Homom(ri);
 I := Grp(rifac);

 if not IsPcGroup(I) or IsCyclic(I) then
   riker := KernelRecogNode(ri);
   SetKernelRecogNode(ri,RefineElementaryAbelianLayers(riker));
   if KernelRecogNode(ri)<>fail then
     SetNiceGenerators(ri,Concatenation(PreImagesOfNiceGeneratorsOfImageNode(ri),NiceGenerators(KernelRecogNode(ri))));
   else
     SetNiceGenerators(ri,PreImagesOfNiceGeneratorsOfImageNode(ri));
   fi;
   return ri;
 fi;

 AcGens := ConstructActionMatrices(ri);
 p := I!.Pcgs!.RelativeOrders[1];
 M := GModuleByMats(Z(p)^0*AcGens,GF(p));

 #if the module is irreducible then the ChiefSeries can't be refined.
 if MTX.IsIrreducible(M) then
   riker := KernelRecogNode(ri);
   SetKernelRecogNode(ri,RefineElementaryAbelianLayers(riker));
   if KernelRecogNode(ri)<>fail then
     SetNiceGenerators(ri,Concatenation(PreImagesOfNiceGeneratorsOfImageNode(ri),NiceGenerators(KernelRecogNode(ri))));
   else
     SetNiceGenerators(ri,PreImagesOfNiceGeneratorsOfImageNode(ri));
   fi;

   return ri;
 fi;

 CS := MTX.BasesCompositionSeries(M);


# get the list of normal subgroups

  L := List([Length(CS),Length(CS)-1..1],i->
SubgroupNC(Grp(ImageRecogNode(ri)),List(CS[i],v->VectortoPc(v,Grp(ImageRecogNode(ri))))));

  maps := List([1..Length(L)-1],i->NaturalHomomorphismByNormalSubgroupNC(L[i],L[i+1]));
  ri := InsertSubTree(ri, rifac, maps);;
  riker := KernelRecogNode(ri);
  SetKernelRecogNode(ri,RefineElementaryAbelianLayers(riker));
  SetParentRecogNode(KernelRecogNode(ri),ri);
  if KernelRecogNode(ri)<>fail then
    SetNiceGenerators(ri,Concatenation(PreImagesOfNiceGeneratorsOfImageNode(ri),NiceGenerators(KernelRecogNode(ri))));
  else
    SetNiceGenerators(ri,PreImagesOfNiceGeneratorsOfImageNode(ri));
  fi;

  return ri;
end;

RemoveTrivialLayers := function(ri)
# Removes the trivial layers
 local rifac,riker,I,parri,newriker;

 if ri=fail then return ri; fi;

 rifac := ImageRecogNode(ri);;
 riker := KernelRecogNode(ri);;
 I := Grp(rifac);
 if IsPcGroup(I) and IsTrivial(I) then
# I is trivial!!
   if HasParentRecogNode(ri) then
     parri := StructuralCopy(ParentRecogNode(ri));
   fi;
   ri := riker;;
   if IsBound(parri) then
     SetParentRecogNode(ri,parri);
   else
     Unbind(ri!.ParentRecogNode);
     ResetFilterObj(ri, HasParentRecogNode);
   fi;
   newriker := KernelRecogNode(ri);
   SetKernelRecogNode(ri,RemoveTrivialLayers(newriker));
   if KernelRecogNode(ri)<>fail then
     SetNiceGenerators(ri,Concatenation(PreImagesOfNiceGeneratorsOfImageNode(ri),NiceGenerators(KernelRecogNode(ri))));
   else
     SetNiceGenerators(ri,PreImagesOfNiceGeneratorsOfImageNode(ri));
   fi;

   return RemoveTrivialLayers(ri);
 fi;

 SetKernelRecogNode(ri,RemoveTrivialLayers(riker));
 if KernelRecogNode(ri)<>fail then
   SetNiceGenerators(ri,Concatenation(PreImagesOfNiceGeneratorsOfImageNode(ri),NiceGenerators(KernelRecogNode(ri))));
 else
   SetNiceGenerators(ri,PreImagesOfNiceGeneratorsOfImageNode(ri));
 fi;
 return ri;
end;
