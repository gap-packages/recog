#
gap> START_TEST("basic.tst");

# Test for MovesOnlySmallPoints:
gap> g := SymmetricGroup(5);;
gap> ri := RECOG.TestGroup(g,false,120);;

# Test for Giant:
gap> g := SymmetricGroup(11);;
gap> ri := RECOG.TestGroup(g,false,Factorial(11));;

# Test for NonTransitive:
gap> g := DirectProduct(SymmetricGroup(5),SymmetricGroup(6));;
gap> ri := RECOG.TestGroup(g,false,Factorial(5)*Factorial(6));;

# Test for Imprimitive:
gap> g := WreathProduct(SymmetricGroup(5),SymmetricGroup(12));;
gap> ri := RECOG.TestGroup(g,false,Factorial(5)^12*Factorial(12));;

# Test for MovesOnlySmallPoints:
gap> g := WreathProduct(SymmetricGroup(2),SymmetricGroup(100));;
gap> ri := RECOG.TestGroup(g,false,Factorial(2)^100*Factorial(100));;

# Test for MovesOnlySmallPoints:
gap> g := WreathProduct(SymmetricGroup(5),SymmetricGroup(32));;
gap> ri := RECOG.TestGroup(g,false,Factorial(5)^32*Factorial(32));;

# Test for MovesOnlySmallPoints:
gap> g := WreathProduct(AlternatingGroup(5),SymmetricGroup(32));;
gap> ri := RECOG.TestGroup(g,false,(Factorial(5)/2)^32 * Factorial(32));;

# Test for Pcgs: S4^10
gap> g := SymmetricGroup(4);;
gap> g := DirectProduct(g,g);;
gap> g := DirectProduct(g,g);;
gap> g := DirectProduct(g,g);;
gap> g := DirectProduct(g,g);;
gap> g := DirectProduct(g,g);;
gap> ri := RECOG.TestGroup(g,false,24^32);;

# Test for ThrowAwayFixedPoints:
gap> g := Group( (100,101,102,103,104,105,106,107,108,109,110), (100,101) );;
gap> ri := RECOG.TestGroup(g,false,Factorial(11), rec(tryNonGroupElements := true));;

# Test for ThrowAwayFixedPoints 2:
gap> x := PermList(Concatenation([2..1000],[1],[1002,1003,1001]))^1000;;
gap> y := PermList(Concatenation([2..1000],[1],[1001,1002,1004,1005,1003]))^1000;;
gap> g := Group( x,y );;
gap> ri := RECOG.TestGroup(g,false,60, rec(tryNonGroupElements := true));;

#
gap> gg := PrimitiveGroup(102,1);;
gap> gg := Group(GeneratorsOfGroup(gg));;
gap> s := Group( (1,2,3,4,5),(1,2) );;
gap> g := WreathProduct(gg,s);;
gap> ri := RECOG.TestGroup(g,false,10549656361799516160);;

#
gap> STOP_TEST("basic.tst");
