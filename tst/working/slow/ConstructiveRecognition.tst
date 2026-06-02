gap> START_TEST("bugfix.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);

# Tests for special linear groups
gap> for d in [10,23,60] do
>   for p in [2,3,5,7,11] do
>       for k in [1,2,3] do
>           if p^k < 256 then
>               G := SL(d,p^k);
>               g := PseudoRandom(GL(d,p^k));
>               G := G^g;
>               res := RECOG.FindStdGens_SL(G);
>               slp := res.slpstd;; bc := res.basi;;
>               res2 := ResultOfStraightLineProgram(slp,GeneratorsOfGroup(G));
>               StdGens := RECOG.MakeSL_StdGens(p,k,d,d).all;
>               for e in [1..Size(res2)] do
>                   Assert(0, res2[e]^bc = StdGens[e]);
>               od;
>           fi;
>       od;
>    od;
> od;

# Tests for symplectic groups
gap> for d in [10,20,60] do
>   for p in [5,7,11] do
>       for k in [1,2,3] do
>           if p^k < 256 then
>               G := Sp(d,p^k);
>               g := PseudoRandom(Sp(d,p^k));
>               G := G^g;
>               i := 1;
>               res := fail;
>               while i < 20 and res = fail do
>                   res := RECOG.FindStdGens_Sp(G);
>               od;
>               if not(res = fail) then
>                   slp := res.slpstd;; bc := res.basi;;
>                   res2 := ResultOfStraightLineProgram(slp,GeneratorsOfGroup(G));
>                   StdGens := RECOG.MakeSp_StdGens(p,k,d,d).all;
>                   for e in [1..Size(res2)-1] do
>                       Assert(0, res2[e]^bc = StdGens[e]);
>                   od;
>               else
>                   Error("something is wrong");
>               fi;
>           fi;
>       od;
>    od;
> od;

# Tests for unitary groups
gap> for d in [10,20,60,11,21,61] do
>   for p in [5,7,11] do
>           if p^2 < 256 then
>               G := SU(d,p);
>               g := PseudoRandom(SU(d,p));
>               G := G^g;
>               i := 1;
>               res := fail;
>               while i < 20 and res = fail do
>                   res := RECOG.FindStdGens_SU(G);
>               od;
>               if not(res = fail) then
>                   slp := res.slpstd;; bc := res.basi;;
>                   res2 := ResultOfStraightLineProgram(slp,GeneratorsOfGroup(G));
>                   StdGens := RECOG.MakeSU_StdGens(p,k,d,d).all;
>                   for e in [1..Size(res2)-1] do
>                       Assert(0, res2[e]^bc = StdGens[e]);
>                   od;
>               else
>                   Error("something is wrong");
>              fi;
>          fi;
>    od;
> od;

# Tests for orthogonal groups

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("bugfix.tst");
