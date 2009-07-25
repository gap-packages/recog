# Test for trivial group:
LoadPackage("recog");
Print("Test: PermTrivial\n");
g := Group( () );
ri := RECOG.TestGroup(g,false,1);
