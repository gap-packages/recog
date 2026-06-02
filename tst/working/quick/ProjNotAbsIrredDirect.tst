gap> START_TEST("ProjNotAbsIrredDirect.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);;
gap> TestSemilinearRewritePair := function(q, d)
>   local badbase, badbaseinput, badext, badextinput, basefld, b, dim,
>         extfld, gens, good, goodimg, h, hgens, i, id, lambda, m, r;
>   basefld := GF(q);
>   extfld := GF(q^d);
>   b := Basis(AsField(basefld, extfld));
>   h := GL(2, q^d);
>   hgens := GeneratorsOfGroup(h);
>   gens := List(hgens, x -> BlownUpMat(b, x));
>   m := GModuleByMats(gens, basefld);
>   r := RECOG.WriteOverBiggerFieldWithSmallerDegreeFinder(m);
>   if r.inforec.d <> d or r.inforec.newdim <> 2 then
>     return false;
>   fi;
>   if Length(r.newgens) <> Length(gens) then
>     return false;
>   fi;
>   if not ForAll(r.newgens, x -> NrRows(x) = 2 and NrCols(x) = 2) then
>     return false;
>   fi;
>   if not ForAll([1 .. Length(gens)],
>                 i -> RECOG.WriteOverBiggerFieldWithSmallerDegree(
>                        r.inforec, gens[i]) = r.newgens[i]) then
>     return false;
>   fi;
>   good := gens[1] * gens[2];
>   goodimg := RECOG.WriteOverBiggerFieldWithSmallerDegree(r.inforec, good);
>   if goodimg = fail or goodimg <> r.newgens[1] * r.newgens[2] then
>     return false;
>   fi;
>   lambda := Z(q^d);
>   if RECOG.WriteOverBiggerFieldWithSmallerDegree(r.inforec, lambda * good)
>      = fail then
>     return false;
>   fi;
>   if not IsEqualProjective(
>            goodimg,
>            RECOG.WriteOverBiggerFieldWithSmallerDegree(
>              r.inforec, lambda * good)) then
>     return false;
>   fi;
>   dim := NrRows(gens[1]);
>   id := IdentityMat(dim, basefld);
>   if RECOG.WriteOverBiggerFieldWithSmallerDegree(r.inforec, id)
>      <> IdentityMat(2, extfld) then
>     return false;
>   fi;
>   if RECOG.WriteOverBiggerFieldWithSmallerDegree(r.inforec, lambda * id)
>      <> IdentityMat(2, extfld) then
>     return false;
>   fi;
>   badbase := IdentityMat(dim, basefld);
>   badbase[2][1] := badbase[2][1] + One(basefld);
>   badbaseinput := r.inforec.basi * badbase * r.inforec.bas;
>   if RECOG.WriteOverBiggerFieldWithSmallerDegree(r.inforec, badbaseinput)
>      <> fail then
>     return false;
>   fi;
>   if RECOG.WriteOverBiggerFieldWithSmallerDegree(
>        r.inforec, lambda * badbaseinput) <> fail then
>     return false;
>   fi;
>   badext := IdentityMat(dim, extfld);
>   badext[1][2] := lambda;
>   badextinput := r.inforec.basi * badext * r.inforec.bas;
>   if RECOG.WriteOverBiggerFieldWithSmallerDegree(r.inforec, badextinput)
>      <> fail then
>     return false;
>   fi;
>   return true;
> end;;
gap> smallPairs := [ [2,2], [4,2], [5,2] ];;
gap> ForAll(smallPairs, pair -> TestSemilinearRewritePair(pair[1], pair[2]));
true
gap> mixedPairs := [ [2,10], [4,6], [5,6], [25,2], [37,2] ];;
gap> ForAll(mixedPairs, pair -> TestSemilinearRewritePair(pair[1], pair[2]));
true
gap> largePairs := [ [257,2] ];;
gap> ForAll(largePairs, pair -> TestSemilinearRewritePair(pair[1], pair[2]));
true
gap> SetInfoLevel(InfoRecog, oldInfoLevel);;
gap> STOP_TEST("ProjNotAbsIrredDirect.tst");
