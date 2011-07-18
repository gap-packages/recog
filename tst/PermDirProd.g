LoadPackage("recog");
g := DirectProduct(SymmetricGroup(12),SymmetricGroup(5));
Print("Testing direct products in permutation groups:\n");
ri := RECOG.TestGroup(g,false,57480192000);
Print("\n");
