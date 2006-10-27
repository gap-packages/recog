#############################################################################
##
##  read.g                recog package
##                                                        Max Neunhoeffer
##                                                            Ákos Seress
##                                                                 et al.
##
##  Copyright 2005-2006 Lehrstuhl D für Mathematik, RWTH Aachen
##
##  Reading the implementation part of the recog package.
##
#############################################################################

# Permutations:
ReadPackage("recog","gap/recoggiant.gi");
ReadPackage("recog","gap/snksetswrsr.gi");
ReadPackage("recog","gap/perm.gi");

# Up to now there is not much here:
ReadPackage("recog","gap/blackbox.gi");

# Matrices/Projective:
ReadPackage("recog","gap/matimpr.gi");
ReadPackage("recog","gap/c6.gi");
ReadPackage("recog","gap/tensor.gi");
ReadPackage("recog","gap/shortorbs.gi");
ReadPackage("recog","gap/forms.gi");
ReadPackage("recog","gap/classical.gi");
ReadPackage("recog","gap/slconstr.gi");
ReadPackage("recog","gap/twoelorders.gi");
ReadPackage("recog","gap/derived.gi");
ReadPackage("recog","gap/semilinear.gi");
ReadPackage("recog","gap/subfield.gi");

# All the method installations are now here:
ReadPackage("recog","gap/matrix.gi");
ReadPackage("recog","gap/projective.gi");

