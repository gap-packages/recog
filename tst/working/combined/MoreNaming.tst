#
# This file contains additional tests for the naming (= non-constructive
# recognition) algorithms implemented in the RecogniseClassical function,
# focused on testing exceptions
#

# Read some helper functions
gap> ReadPackage("recog", "tst/naming.g");
true

#
# Defined group TODO to test case TODO
#
gap> G := Group( [ [[1,1],[0,1]], [[1,0],[1,1]] ] * Z(2));;
gap> r := RecogniseClassical(G);;
gap> r.isSLContained;
"unknown"
