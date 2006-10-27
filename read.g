#############################################################################
##
##  read.g                recogbase package
##                                                        Max Neunhoeffer
##                                                            Ákos Seress
##
##  Copyright 2005-2006 Lehrstuhl D für Mathematik, RWTH Aachen
##
##  Reading the implementation part of the recogbase package.
##
#############################################################################

ReadPackage("recog","gap/libhacks.gi");   # This should go in the future!

# Generic:
ReadPackage("recogbase","gap/methsel.gi");
ReadPackage("recogbase","gap/recognition.gi");

# The following contain generic functionality for different types of groups:

# Permutations:
ReadPackage("recogbase","gap/perm.gi");
# Matrices/Projective:
ReadPackage("recogbase","gap/matrix.gi");
ReadPackage("recogbase","gap/projective.gi");
# Black box:
ReadPackage("recogbase","gap/blackbox.gd");

# Note: Nearly all methods are now in the "recog" package.
