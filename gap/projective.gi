#############################################################################
##
##  projective.gi      
##                                recog package
##                                                        Max Neunhoeffer
##                                                            Ákos Seress
##
##  Copyright 2006-2008 by the authors.
##  This file is free software, see license information at the end.
##
##  A collection of find homomorphism methods for projective groups.
##
#############################################################################

SLPforElementFuncsProjective.TrivialProjectiveGroup :=
   function(ri,g)
     return StraightLineProgramNC( [ [1,0] ], 1 );
   end;

FindHomMethodsProjective.TrivialProjectiveGroup := function(ri, G)
  local g,gens;
  gens := GeneratorsOfGroup(G);
  for g in gens do
      if not(IsOneProjective(g)) then
          return false;
      fi;
  od;
  SetSize(ri,1);
  Setslpforelement(ri,SLPforElementFuncsProjective.TrivialProjectiveGroup);
  Setslptonice( ri, 
                StraightLineProgramNC([[[1,0]]],Length(GeneratorsOfGroup(G))));
  SetFilterObj(ri,IsLeaf);
  return true;
end;

FindHomMethodsProjective.BlocksModScalars := function(ri,G)
  # We assume that ri!.blocks is a list of ranges where the diagonal
  # blocks are. Note that their length does not have to sum up to 
  # the dimension, because some blocks at the end might already be trivial.
  # Note further that in this method it is understood that G should *neither*
  # be recognised as a matrix group *nor* as a projective group. Rather,
  # all "block-scalars" shall be ignored. This method is only used when
  # used as a hint by FindHomMethodsMatrix.BlockDiagonal!
  local H,data,hom,middle,newgens,nrblocks,topblock;
  nrblocks := Length(ri!.blocks);  # this is always >= 1
  if ForAll(ri!.blocks,b->Length(b)=1) then
      # All blocks are projectively trivial, so nothing to do here:
      SetSize(ri,1);
      Setslpforelement(ri,SLPforElementFuncsProjective.TrivialProjectiveGroup);
      Setslptonice( ri, StraightLineProgramNC([[[1,0]]],
                                              Length(GeneratorsOfGroup(G))));
      SetFilterObj(ri,IsLeaf);
      ri!.comment := "_BlocksDim=1";
      return true;
  fi;
      
  if nrblocks = 1 then   # in this case the block is everything!
      # no hints for the factor, will run into diagonal and notice scalar
      data := rec(poss := ri!.blocks[1]);
      newgens := List(GeneratorsOfGroup(G),x->RECOG.HomToDiagonalBlock(data,x));
      H := GroupWithGenerators(newgens);
      hom := GroupHomByFuncWithData(G,H,RECOG.HomToDiagonalBlock,data);
      Sethomom(ri,hom);
      # The following is already be set, but make it explicit here:
      Setmethodsforfactor(ri,FindHomDbProjective);
      # no kernel:
      findgensNmeth(ri).method := FindKernelDoNothing;
      return true;
  fi;
  # Otherwise more than one block, cut in half:
  middle := QuoInt(nrblocks,2)+1;   # the first one taken
  topblock := ri!.blocks[nrblocks];
  data := rec(poss := [ri!.blocks[middle][1]..topblock[Length(topblock)]]);
  newgens := List(GeneratorsOfGroup(G),x->RECOG.HomToDiagonalBlock(data,x));
  H := GroupWithGenerators(newgens);
  hom := GroupHomByFuncWithData(G,H,RECOG.HomToDiagonalBlock,data);
  Sethomom(ri,hom);

  # the factor are the last few blocks:
  # The following is already be set, but make it explicit here:
  Setmethodsforfactor(ri,FindHomDbProjective);
  if middle < nrblocks then   # more than one block in factor:
      forfactor(ri).blocks := List(ri!.blocks{[middle..nrblocks]},
                                   x->x - (ri!.blocks[middle][1]-1));
      Add(forfactor(ri).hints,
          rec( method := FindHomMethodsProjective.BlocksModScalars,rank := 2000,
               stamp := "BlocksModScalars" ),1);
  fi; # Otherwise the factor is to be recognised projectively as usual

  # the kernel is the first few blocks:
  findgensNmeth(ri).args[1] := 5 + nrblocks;
  findgensNmeth(ri).args[2] := 5 + middle - 1;
  # The following is already set, but make it explicit here:
  forkernel(ri).blocks := ri!.blocks{[1..middle-1]};
  Add(forkernel(ri).hints,
      rec( method := FindHomMethodsProjective.BlocksModScalars, rank := 2000,
           stamp := "BlocksModScalars" ),1);
  Setimmediateverification(ri,true);
  return true;
end;

SLPforElementFuncsProjective.StabilizerChain := function(ri,x)
  local r;
  r := SiftGroupElementSLP(ri!.stabilizerchain,x);
  return r.slp;
end;

FindHomMethodsProjective.StabilizerChain := function(ri,G)
  local Gm,S,d,f,opt,q;
  d := DimensionOfMatrixGroup(G);
  f := FieldOfMatrixGroup(G);
  q := Size(f);
  opt := rec( Projective := true );
  #if q^(d-1) > 100000 then
  #    opt.TryShortOrbit := 5;
  #fi;
  Gm := GroupWithMemory(G);
  S := StabilizerChain(Gm,opt);
  SetSize(ri,Size(S));
  ri!.stabilizerchain := S;
  Setslptonice(ri,SLPOfElms(StrongGenerators(S)));
  ForgetMemory(S);
  Setslpforelement(ri,SLPforElementFuncsProjective.StabilizerChain);
  SetFilterObj(ri,IsLeaf);
  return true;
end;

RECOG.HomProjDet := function(data,m)
  return data.c ^ (LogFFE(DeterminantMat(m),data.z) mod data.gcd);
end;

FindHomMethodsProjective.ProjDeterminant := function(ri,G)
  local H,c,d,detsadd,f,gcd,hom,newgens,q,z;
  f := FieldOfMatrixGroup(G);
  d := DimensionOfMatrixGroup(G);
  q := Size(f);
  gcd := GcdInt(q-1,d);
  if gcd = 1 then return false; fi;
  z := Z(q);
  detsadd := List(GeneratorsOfGroup(G),x->LogFFE(DeterminantMat(x),z) mod gcd);
  if IsZero(detsadd) then return false; fi;
  c := PermList(Concatenation([2..gcd],[1]));
  newgens := List(detsadd,x->c^x);
  H := GroupWithGenerators(newgens);
  hom := GroupHomByFuncWithData(G,H,RECOG.HomProjDet,
                                rec(c := c, z := z, gcd := gcd));
  Sethomom(ri,hom);
  Setmethodsforfactor(ri,FindHomDbPerm);
  findgensNmeth(ri).args[1] := 8;
  findgensNmeth(ri).args[2] := 5;
  Setimmediateverification(ri,true);
  return true;
end;

RECOG.HomNormLastBlock := function(data,x)
  local pos;
  pos := data!.blocks[Length(data!.blocks)][1];
  if not(IsOne(x[pos][pos])) then
      x := (x[pos][pos]^-1)*x;
  fi;
  return x;
end;

FindHomMethodsProjective.BlockScalarProj := function(ri,G)
  # We just norm the last block and go to matrix methods.
  local H,data,hom,newgens;
  data := rec( blocks := ri!.blocks );
  newgens := List(GeneratorsOfGroup(G),x->RECOG.HomNormLastBlock(data,x));
  H := GroupWithGenerators(newgens);
  hom := GroupHomByFuncWithData(G,H,RECOG.HomNormLastBlock,data);
  Sethomom(ri,hom);

  findgensNmeth(ri).method := FindKernelDoNothing;  # This is an iso

  # Switch to matrix mode:
  Setmethodsforfactor(ri,FindHomDbMatrix);
  Add(forfactor(ri).hints,
      rec( method := FindHomMethodsMatrix.BlockScalar, rank := 2000,
           stamp := "BlockScalar" ), 1);
  forfactor(ri).blocks := ri!.blocks{[1..Length(ri!.blocks)-1]};
  return true;
end;

# Looking at element orders:

SporadicsElementOrders :=
[ [ 1,2,3,5,6,7,10,11,15,19 ],[ 1,2,3,4,5,6,8,11 ],
  [ 1,2,3,4,5,6,8,10,11 ], [ 1,2,3,4,5,6,8,9,10,12,15,17,19 ],
  [ 1,2,3,4,5,6,7,8,11,14,15,23 ],[ 1,2,3,4,5,6,7,8,11 ],
  [ 1,2,3,4,5,6,7,8,10,12,15 ], [ 1,2,3,4,5,6,7,8,10,12,14,15,17,21,28 ],
  [ 1,2,3,4,5,6,7,8,10,12,13,14,15,16,20,24,26,29 ],
  [ 1,2,3,4,5,6,7,8,10,11,12,15,20 ], [ 1,2,3,4,5,6,7,8,10,11,12,14,15,21,23 ],
  [ 1,2,3,4,5,6,7,8,10,11,12,14,15,16,20,21,22,23,24,28,
      29,30,31,33,35,37,40,42,43,44,66 ],
  [ 1,2,3,4,5,6,7,8,10,11,12,14,15,16,19,20,28,31 ],
  [ 1,2,3,4,5,6,7,8,9,10,12,13,14,15,18,19,20,21,24,27, 28,30,31,36,39 ],
  [ 1,2,3,4,5,6,7,8,9,10,11,12,14,15,30 ],
  [ 1,2,3,4,5,6,7,8,9,10,11,12,14,15,19,20,21,22,25,30, 35,40 ],
  [ 1,2,3,4,5,6,7,8,9,10,11,12,14,15,18,20,21,22,24,25,
      28,30,31,33,37,40,42,67 ],
  [ 1,2,3,4,5,6,7,8,9,10,11,12,14,15,18,20,21,22,23,24,30 ],
  [ 1,2,3,4,5,6,7,8,9,10,11,12,14,15,16,18,20,23,24,28,30 ],
  [ 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,18,20,21,24 ],
  [ 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,18,20,21,22,24,30 ],
  [ 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,18,20,21,22,
      23,24,26,28,30,33,35,36,39,40,42,60 ],
  [ 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,20,21,
      22,23,24,26,27,28,30,35,36,39,42,60 ],
  [ 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,20,21,
      22,23,24,26,27,28,29,30,33,35,36,39,42,45,60 ],
  [ 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,
      21,22,23,24,25,26,27,28,30,31,32,33,34,35,36,38,39,40,
      42,44,46,47,48,52,55,56,60,66,70 ],
  [ 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,
      21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,38,39,
      40,41,42,44,45,46,47,48,50,51,52,54,55,56,57,59,60,62,
      66,68,69,70,71,78,84,87,88,92,93,94,95,104,105,110,119 ] ];
SporadicsProbabilities :=
[ [ 1/175560,1/120,1/30,1/15,1/6,1/7,1/5,1/11,2/15,3/19 ],
  [ 1/7920,1/48,1/18,1/8,1/5,1/6,1/4,2/11 ],
  [ 1/95040,3/320,5/108,1/16,1/10,1/4,1/4,1/10,2/11 ],
  [ 1/50232960,1/1920,49/9720,1/96,1/15,1/24,1/8,1/9,1/5,1/12,2/15,
      2/17,2/19 ],
  [ 1/10200960,1/2688,1/180,1/32,1/15,1/12,1/7,1/8,2/11,1/7,2/15,
      2/23 ],[ 1/443520,1/384,1/36,3/32,1/5,1/12,2/7,1/8,2/11 ],
  [ 1/604800,3/640,31/1080,1/96,7/150,1/8,1/7,1/8,3/10,1/12,2/15 ],
  [ 1/4030387200,17/322560,2/945,1/84,1/300,1/18,95/4116,1/16,1/20,
      1/6,5/28,1/15,2/17,4/21,1/14 ],
  [ 1/145926144000,283/22364160,1/2160,17/5120,13/3000,1/48,1/28,
      11/192,3/40,1/8,1/52,3/28,1/15,1/8,3/20,1/12,3/52,2/29 ],
  [ 1/44352000,11/23040,1/360,19/960,17/375,5/72,1/7,3/16,1/10,2/11,
      1/12,1/15,1/10 ],
  [ 1/244823040,19/107520,11/3780,1/48,1/60,1/12,1/21,1/16,1/20,
      1/11,1/6,1/7,2/15,2/21,2/23 ],
  [ 1/86775571046077562880,13/21799895040,1/2661120,53/1576960,1/6720,
      2311/2661120,1/420,31/7680,13/960,133/31944,1/32,5/84,1/30,
      1/32,1/80,1/21,13/264,1/23,1/24,1/14,1/29,1/30,3/31,1/33,
      2/35,3/37,1/20,1/21,3/43,1/44,1/33 ],
  [ 1/460815505920,1/161280,1/3240,79/20160,1/180,1/72,29/1372,1/16,
      1/20,1/11,1/36,1/28,2/45,1/4,3/19,1/10,1/14,2/31 ],
  [ 1/90745943887872000,1/92897280,13603/1719506880,257/1935360,1/3000,
      67/25920,1/1176,5/384,5/648,1/120,25/432,1/39,1/56,1/15,5/72,
      1/19,1/20,1/21,1/6,1/9,1/28,1/15,2/31,1/12,2/39 ],
  [ 1/898128000,1/40320,31/29160,1/96,31/750,11/360,1/7,1/8,2/27,
      1/30,2/11,1/12,1/7,1/15,1/15 ],
  [ 1/273030912000000,131/473088000,59/1632960,23/46080,16913/31500000,
      1/192,1/420,9/320,1/27,431/12000,1/22,17/144,1/28,13/180,2/19,
      3/20,1/21,1/22,2/25,1/12,2/35,1/20 ],
  [ 1/51765179004000000,1/39916800,15401/2694384000,1/20160,601/2250000,
      1291/362880,1/168,1/80,1/54,73/3600,1/33,5/288,1/168,28/1125,
      1/18,1/40,1/21,1/11,1/8,1/25,1/28,1/45,5/31,2/33,2/37,1/20,
      1/21,3/67 ],
  [ 1/495766656000,179/31933440,631/2449440,1/1440,1/250,373/12960,
      1/42,1/24,1/54,1/15,1/11,1/18,1/14,1/10,1/18,1/10,1/21,1/11,
      2/23,1/12,1/30 ],
  [ 1/42305421312000,523/743178240,1/116640,139/120960,1/500,79/12960,
      1/56,5/192,1/54,1/20,1/11,2/27,5/56,1/10,1/16,1/18,1/10,
      2/23,1/12,1/28,1/10 ],
  [ 1/448345497600,151/23224320,661/1959552,103/23040,7/1800,187/10368,
      1/84,5/96,1/27,3/40,1/11,31/288,2/13,1/28,1/9,1/9,1/20,2/21,
      1/24 ],
  [ 1/64561751654400,4297/7357464576,11419/176359680,181/276480,1/600,
      9121/933120,1/42,17/384,5/108,1/24,1/11,79/864,2/13,1/14,1/30,
      1/16,7/108,1/20,1/21,1/11,1/24,1/30 ],
  [ 1/4157776806543360000,39239/12752938598400,7802083/4035109478400,
      1061/11612160,1433/15120000,198391/69672960,2/2205,79/23040,1/216,
      109/9600,1/66,10949/207360,1/156,1/42,277/5400,1/32,1/24,
      37/480,17/252,1/22,2/23,25/288,1/52,1/14,13/120,1/33,1/35,
      1/36,2/39,1/40,1/84,1/60 ],
  [ 1/4089470473293004800,407161/129123503308800,161281/148565394432,
      239/5806080,1/25200,1036823/705438720,1/840,1/128,127/17496,
      11/1200,1/44,529/12960,1/39,5/168,1/72,1/16,1/17,13/216,1/30,
      1/42,3/44,2/23,1/16,1/13,1/27,1/28,7/120,1/35,1/18,2/39,
      1/42,1/60 ],
  [ 1/1255205709190661721292800,6439/1032988026470400,144613199/
        4412392214630400,25/6967296,1/907200,159797/564350976,67/123480,
      11/4608,1189/1049760,7/4800,1/132,4741/311040,1/234,5/168,
      103/16200,1/32,1/17,11/288,1/48,17/252,1/44,2/23,7/72,1/26,
      1/27,1/28,2/29,1/24,2/33,1/35,1/24,4/117,5/84,2/45,1/60 ],
  [ 1/4154781481226426191177580544000000,
      34727139371/281639525236291462496256000,160187/10459003768012800,
      56445211/3060705263616000,1873/11088000000,7216687/1418939596800,
      1/564480,18983/123863040,5/34992,667/2688000,1/1320,12629/3732480,
      1/312,871/564480,31/3600,1/96,1/68,7/432,1/38,323/12000,1/252,
      5/264,1/23,19/432,1/25,3/104,1/27,5/224,67/1200,2/31,1/32,
      1/66,3/68,1/70,5/108,1/38,1/39,1/20,1/36,1/44,1/23,2/47,
      1/48,1/52,1/55,1/56,1/30,1/66,1/70 ],
  [ 1/808017424794512875886459904961710757005754368000000000,
      952987291/132953007399245638117682577408000000,
      1309301528411/299423045898886400305790976000,
      228177889/1608412858851262464000,361177/34128864000000000,
      352968797/83672030144102400,16369/1382422809600,80467/177124147200,
      7/18895680,1270627/532224000000,1/1045440,20669/313528320,
      31/949104,9/250880,8611/40824000,1/3072,1/2856,91/139968,1/1140,
      2323/1152000,907/370440,3/3520,1/276,167/13824,1/250,1/208,
      1/162,3/392,1/87,529/43200,1/93,1/64,5/1188,1/136,31/2100,
      1/48,1/76,25/702,49/1600,1/41,1/56,1/176,1/135,3/92,1/47,
      1/96,1/50,1/51,3/104,1/54,1/110,5/112,1/57,2/59,41/720,1/31,
      1/44,1/68,2/69,3/140,2/71,1/26,1/28,2/87,1/44,1/46,2/93,
      1/47,2/95,1/52,1/105,1/110,2/119 ] ];
SporadicsNames :=
[ "J1","M11","M12","J3","M23","M22","J2","He","Ru","HS","M24",
  "J4","ON","Th","McL","HN","Ly","Co3","Co2","Suz","Fi22","Co1",
  "Fi23","F3+","B","M" ];
SporadicsSizes :=
[ 175560, 7920, 95040, 50232960, 10200960, 443520, 604800, 4030387200, 
  145926144000, 44352000, 244823040, 86775571046077562880, 460815505920, 
  90745943887872000, 898128000, 273030912000000, 51765179004000000, 
  495766656000, 42305421312000, 448345497600, 64561751654400, 
  4157776806543360000, 4089470473293004800, 1255205709190661721292800, 
  4154781481226426191177580544000000, 
  808017424794512875886459904961710757005754368000000000 ];
SporadicsKillers :=
[ ,,,,,,,,,,,,,,,,,,,,[[18..22]],[[26..32],[25..32]],
  [[28..32],[27..32]],[[27..35],[29..35],[27,29,34]], # the latter is for Fi23
  [[31..49],[40,41,42,43,44,45,46,48,49]],   # the latter is against Fi23
  [[32..73],[61..73]] ];
SporadicsWorkers := [];
SporadicsWorkers[2] := SporadicsWorkerGenSift;   # M11
SporadicsWorkers[3] := SporadicsWorkerGenSift;   # M12
SporadicsWorkers[6] := SporadicsWorkerGenSift;   # M22
SporadicsWorkers[7] := SporadicsWorkerGenSift;   # J2
SporadicsWorkers[10] := SporadicsWorkerGenSift;  # HS
SporadicsWorkers[17] := SporadicsWorkerGenSift;  # Ly
SporadicsWorkers[18] := SporadicsWorkerGenSift;  # Co3
SporadicsWorkers[19] := SporadicsWorkerGenSift;  # Co2
LastRecognisedSporadic := fail;

FindHomMethodsProjective.LookAtOrders := function(ri,G)
  local i,j,jj,k,killers,l,limit,o,ordersseen,pp,raus,res,x;
  l := [1..26];
  pp := 0*[1..26];
  ordersseen := [];
  for i in [1..120] do
      x := PseudoRandom(G);
      o := RECOG.ProjectiveOrder(x);
      AddSet(ordersseen,o);
      Info(InfoRecog,3,"Found order: ",String(o,3)," (element #",i,")");
      l := Filtered(l,i->o in SporadicsElementOrders[i]);
      if l = [] then
          LastRecognisedSporadic := fail;
          return false;
      fi;
      # Throw out improbable ones:
      j := 1;
      while j <= Length(l) do
          if Length(l) = 1 then
              limit := 1/1000;
          else
              limit := 1/400;
          fi;
          jj := l[j];
          raus := false;
          for k in [1..Length(SporadicsElementOrders[jj])] do
              if not(SporadicsElementOrders[jj][k] in ordersseen) and
                 (1-SporadicsProbabilities[jj][k])^i < limit then
                  Info(InfoRecog,3,"Have thrown out ",SporadicsNames[jj],
                       " (did not see order ",
                       SporadicsElementOrders[jj][k],")");
                  raus := true;
                  break;
              fi;
          od;
          if not(raus) and IsBound(SporadicsKillers[jj]) then
            for killers in SporadicsKillers[jj] do
              if Intersection(ordersseen,SporadicsElementOrders[jj]{killers})=[]
                 and (1-Sum(SporadicsProbabilities[jj]{killers}))^i < 10^-5 then
                  raus := true;
                  break;
                  Info(InfoRecog,3,"Have thrown out ",SporadicsNames[jj],
                       " (did not see orders in ",
                       SporadicsElementOrders[jj]{killers},")");
              fi;
            od;
          fi;
          if raus then
              Remove(l,j);
          else
              j := j + 1;
          fi;
      od;
      if l = [] then
          LastRecognisedSporadic := fail;
          return false;
      fi;
      if Length(l) = 1 and i > 80 then
          Info(InfoRecog,2,"I guess that this is a projective representation ", 
               "of the sporadic simple group ",SporadicsNames[l[1]],".");
          res := LookupHintForSimple(ri,G,SporadicsNames[l[1]]);
          if res = true then return res; fi;
          if IsBound(SporadicsWorkers[l[1]]) then
              Info(InfoRecog,2,"Calling its installed worker...");
              return SporadicsWorkers[l[1]](SporadicsNames[l[1]],
                                            SporadicsSizes[l[1]],ri,G);
          fi;
          Info(InfoRecog,2,"However, I cannot verify this.");
          LastRecognisedSporadic := SporadicsNames[l[1]];
          return false;
      fi;
      if Length(l) < 6 then
          Info(InfoRecog,3,"Possible sporadics left: ",
               SporadicsNames{l});
      else
          Info(InfoRecog,3,"Possible sporadics left: ",Length(l));
      fi;
  od;
  Info(InfoRecog,2,"Giving up, still possible Sporadics: ",
       SporadicsNames{l});
  LastRecognisedSporadic := fail;
  return false;
end;

# The method installations:

AddMethod( FindHomDbProjective, FindHomMethodsProjective.TrivialProjectiveGroup,
  3000, "TrivialProjectiveGroup",
        "check if all generators are scalar multiples of the identity matrix" );
AddMethod( FindHomDbProjective, FindHomMethodsProjective.ProjDeterminant,
  1300, "ProjDeterminant",
        "find homomorphism to non-zero scalars mod d-th powers" );
# Note that we *can* in fact use the Matrix method here, because it
# will do the right thing when used in projective mode:
AddMethod( FindHomDbProjective, FindHomMethodsProjective.FewGensAbelian,
  1250, "FewGensAbelian",
     "if very few generators, check IsAbelian and if yes, do KnownNilpotent");
AddMethod( FindHomDbProjective, FindHomMethodsMatrix.ReducibleIso,
  1200, "ReducibleIso",
        "use MeatAxe to find a composition series, do base change" );
AddMethod( FindHomDbProjective, FindHomMethodsProjective.NotAbsolutelyIrred,
  1100, "NotAbsolutelyIrred",
        "write over a bigger field with smaller degree" );
AddMethod( FindHomDbProjective, FindHomMethodsProjective.Subfield,
  1000, "Subfield",
        "write over a smaller field with same degree" );
AddMethod( FindHomDbProjective, FindHomMethodsProjective.C3C5,
  900, "C3C5",
        "compute a normal subgroup of derived and resolve C3 and C5" );
#AddMethod( FindHomDbProjective, FindHomMethodsProjective.Derived,
#   900, "Derived",
#        "restrict to derived subgroup" );
# Superseded by C3C5.
AddMethod( FindHomDbProjective, FindHomMethodsProjective.C6,
   850, "C6",
        "find either an (imprimitive) action or a symplectic one" );
AddMethod( FindHomDbProjective, FindHomMethodsProjective.FindEvenNormal,
   825, "FindEvenNormal",
        "find D2, D4 or D7 by finding reducible normal subgroup" );
AddMethod( FindHomDbProjective, FindHomMethodsProjective.D247,
   800, "D247",
        "play games to find a normal subgroup" );
AddMethod( FindHomDbProjective, FindHomMethodsProjective.TensorDecomposable,
   700, "Tensor",
        "find a tensor decomposition" );
AddMethod( FindHomDbProjective, FindHomMethodsProjective.LowIndex,
   600, "LowIndex",
        "find an (imprimitive) action on subspaces" );
# By now we suspect it to be a simple group
AddMethod( FindHomDbProjective, FindHomMethodsProjective.LookAtOrders,
   550, "LookAtOrders",
        "generate a few random elements, calculate LCM of proj. orders" );
AddMethod( FindHomDbProjective, FindHomMethodsProjective.TwoLargeElOrders,
   500, "TwoLargeElOrders",
        "look at two large element orders" );
AddMethod( FindHomDbProjective, FindHomMethodsProjective.StabilizerChain,
   100, "StabilizerChain",
        "last resort: compute a stabilizer chain (projectively)" );

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

