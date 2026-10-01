# Constructive recognition of Sp, SU and Omega in their natural
# representation.  Broken: RECOG.FindStdGens_Sp errors out on Sp(10,3)
# ("no method found" for `*`), hangs on Sp(6,3), and one branch of
# RECOG.FindStdGens_Sp2 still ends in Error("here") followed by
# return "TODO".  RECOG.FindStdGens_Orthogonal has no working entry
# point yet.  The SL case is covered by tst/working/quick/sln.tst.
gap> START_TEST("ConstructiveRecognition.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);

# Tests for symplectic groups
gap> for d in [10,20,60] do
>   for p in [2,3,5,7,11] do
>       for k in [1,2,3] do
>           if p^k < 256 then
>               G := Sp(d,p^k);
>               g := PseudoRandom(GL(d,p^k));
>               G := G^g;
>               i := 1;
>               res := fail;
>               while i < 20 and res = fail do
>                   res := RECOG.FindStdGens_Sp(G);
>                   i := i + 1;
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
>                   i := i + 1;
>               od;
>               if not(res = fail) then
>                   slp := res.slpstd;; bc := res.basi;;
>                   res2 := ResultOfStraightLineProgram(slp,GeneratorsOfGroup(G));
>                   StdGens := RECOG.MakeSU_StdGens(d,p^2,p,2,p).all;
>                   for e in [1..Size(res2)-1] do
>                       Assert(0, res2[e]^bc = StdGens[e]);
>                   od;
>               else
>                   Error("something is wrong");
>              fi;
>          fi;
>    od;
> od;

# Tests for orthogonal groups: none yet, RECOG.FindStdGens_Orthogonal
# does not work for any input we tried.

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("ConstructiveRecognition.tst");
