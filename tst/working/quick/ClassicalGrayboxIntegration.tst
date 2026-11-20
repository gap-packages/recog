gap> START_TEST("ClassicalGrayboxIntegration.tst");

# LieTypeNonConstr passes the socle and matrix field size to the graybox method.
# Wrap the real function so that its arguments and calls can also be checked.
gap> grayboxOriginal := RECOG.RecogniseClassicalGraybox;;
gap> grayboxCalls := 0;;
gap> grayboxLastGroup := fail;;
gap> grayboxLastQ := fail;;
gap> RECOG.RecogniseClassicalGraybox := function(G,q)
>     grayboxCalls := grayboxCalls + 1;
>     grayboxLastGroup := G;
>     grayboxLastQ := q;
>     return grayboxOriginal(G,q);
> end;;

# Without a socle, the graybox method must not be called.
gap> grayboxRi := RecogNode(SL(3,3),true,rec());;
gap> CallRecogMethod(FindHomMethodsProjective.LieTypeNonConstr,grayboxRi) = TemporaryFailure;
true
gap> grayboxCalls;
0

# Exercise the method with different characteristics, field sizes and families.
gap> grayboxCheckMethod := function(G,name)
>     local ri, result;
>     ri := RecogNode(G,true,rec());
>     ri!.simplesocle := G;
>     result := CallRecogMethod(FindHomMethodsProjective.LieTypeNonConstr,ri);
>     return result = TemporaryFailure and IsBound(ri!.comment)
>         and ri!.comment = name;
> end;;
gap> grayboxCheckMethod(SL(3,3),"L3(3)");
true
gap> grayboxCheckMethod(SL(3,4),"L3(4)");
true
gap> grayboxCheckMethod(Sp(6,3),"S6(3)");
true

# The node group is GL(3,3), but the input to graybox must be its SL(3,3) socle.
gap> grayboxRi := RecogNode(GL(3,3),true,rec());;
gap> grayboxRi!.simplesocle := SL(3,3);;
gap> grayboxCalls := 0;;
gap> CallRecogMethod(FindHomMethodsProjective.LieTypeNonConstr,grayboxRi) = TemporaryFailure;
true
gap> grayboxCalls > 0 and IsIdenticalObj(grayboxLastGroup,grayboxRi!.simplesocle)
>     and not IsIdenticalObj(grayboxLastGroup,Grp(grayboxRi)) and grayboxLastQ = 3;
true
gap> RECOG.RecogniseClassicalGraybox := grayboxOriginal;;
gap> STOP_TEST("ClassicalGrayboxIntegration.tst");
