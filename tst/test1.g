# A little test for the recog package
LoadPackage("recog");
Print("Test: S5 wr PrimitiveGroup(102,1)\n");
gg := PrimitiveGroup(102,1);
gg := Group(GeneratorsOfGroup(gg));
s := Group( (1,2,3,4,5),(1,2) );
g := WreathProduct(gg,s);
ri := RECOG.TestGroup(g,false,10549656361799516160);
