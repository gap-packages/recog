# Test for Giant:
LoadPackage("recog");
Print("Test: Giant\n");
g := SymmetricGroup(11);
ri := RECOG.TestGroup(g,false,Factorial(11));
