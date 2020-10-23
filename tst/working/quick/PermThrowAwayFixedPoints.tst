gap> g := Group( (100,101,102), (101,102) );;
gap> RECOG.TestGroup(g, false, 6, rec(tryNonGroupElements := true));;

# Explicitly test failing case
gap> ri := RecogniseGroup(g);;
gap> SLPforElement(ri, (1,2));
fail
