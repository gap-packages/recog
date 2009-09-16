# This tests the non-constructive recognition for the sporadics and friends
# This is not an official test!
for n in RECOG.SporadicsNames{Concatenation([1..23],[27..40])} do
    Print("Groupname: ",n,"\n");
    g := AtlasGenerators(n,1).generators;
    g := Group(g);
    ri := EmptyRecognitionInfoRecord(rec(),g,IsMatrixGroup(g));
    res := FindHomMethodsProjective.SporadicsByOrders(ri,g:DEBUGRECOGSPORADICS);
    if res = false then
        Print(">>>>>FAILURE!!!\n");
    elif Length(res) > 1 then
        Print(">>>>>AMBIGUITY: ",res,"\n");
    else
        Print("Success: ",res,"\n");
    fi; 
od;
