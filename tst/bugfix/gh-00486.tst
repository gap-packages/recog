gap> START_TEST("gh-00486.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);

# matgrp <= 0.70 calls AddMethod with the method API of recog <= 1.4: a
# function of (ri, G) returning true, false or fail, plus stamp and comment.
# See https://github.com/gap-packages/recog/pull/486
gap> hints := [];; seen := false;;
gap> AddMethod(hints, function(ri, G)
>     seen := IsIdenticalObj(G, Grp(ri));
>     return false;
>   end, 5100, "OldApiFalse", "returns false");
gap> AddMethod(hints, function(ri, G) return fail; end,
>   5000, "OldApiFail", "returns fail");
gap> AddMethod(hints, function(ri, G) return NotEnoughInformation; end,
>   4900, "OldApiNotEnough", "returns NotEnoughInformation");
gap> ri := RecogniseGeneric(SL(2,5), FindHomDbMatrix, "", rec(hints := hints));;
gap> seen;
true
gap> IsBound(fhmethsel(ri).inapplicableMethods.OldApiFalse);
true
gap> IsBound(fhmethsel(ri).failedMethods.OldApiFail);
true
gap> IsReady(ri);
true
gap> hints := [];;
gap> AddMethod(hints, function(ri, G)
>     return CallRecogMethod(FindHomMethodsGeneric.TrivialGroup, ri) = Success;
>   end, 5100, "OldApiTrue", "returns true");
gap> ri := RecogniseGeneric(Group(IdentityMat(2, GF(5))), FindHomDbMatrix, "",
>   rec(hints := hints));;
gap> fhmethsel(ri).successMethod;
"OldApiTrue"
gap> IsReady(ri);
true

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("gh-00486.tst");
