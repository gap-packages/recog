#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
##
##  Reading the implementation part of the recog package.
##
#############################################################################

# Generic:
ReadPackage("recog","gap/base/methsel.gi");
ReadPackage("recog","gap/base/recognition.gi");

# The following contain generic functionality for different types of groups:

# Projective:
ReadPackage("recog","gap/base/projective.gi");


# Some tools:
ReadPackage("recog","gap/tools.gi");

# Permutations:
ReadPackage("recog","gap/giant.gi");
ReadPackage("recog","gap/snksetswrsr.gi");

# Up to now there is not much here:
ReadPackage("recog","gap/SnAnBB.gi");

# Matrices/Projective:
ReadPackage("recog","gap/findnormal.gi");
ReadPackage("recog","gap/matimpr.gi");
ReadPackage("recog","gap/c6.gi");
ReadPackage("recog","gap/tensor.gi");
# ReadPackage("recog","gap/forms.gi");
ReadPackage("recog","gap/ppd.gi");
ReadPackage("recog","gap/classical.gi");
ReadPackage("recog","gap/slconstr.gi");
ReadPackage("recog","gap/c3c5.gi");
ReadPackage("recog","gap/d247.gi");
ReadPackage("recog","gap/almostsimple/twoelorders.gi");
ReadPackage("recog","gap/almostsimple.gi");
ReadPackage("recog","gap/almostsimple/lietype.gi");
ReadPackage("recog","gap/almostsimple/hints.gi");
ReadPackage("recog","gap/classicalnatural.gi");
ReadPackage("recog","gap/AnSnOnFDPM.gi");

# All the method installations are now here:
ReadPackage("recog","gap/perm.gi");
ReadPackage("recog","gap/matrix.gi");
ReadPackage("recog","gap/projective.gi");
