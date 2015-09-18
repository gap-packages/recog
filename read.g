#############################################################################
##
##  read.g                recog package
##                                                        Max Neunhoeffer
##                                                            Ákos Seress
##                                                                 et al.
##
##  Copyright 2005-2008 by the authors.
##  This file is free software, see license information at the end.
##
##  Reading the implementation part of the recog package.
##
#############################################################################

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
ReadPackage("recog","gap/blackbox.gi");

##
##  This program is free software: you can redistribute it and/or modify
##  it under the terms of the GNU General Public License as published by
##  the Free Software Foundation, either version 3 of the License, or
##  (at your option) any later version.
##
##  This program is distributed in the hope that it will be useful,
##  but WITHOUT ANY WARRANTY; without even the implied warranty of
##  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
##  GNU General Public License for more details.
##
##  You should have received a copy of the GNU General Public License
##  along with this program.  If not, see <http://www.gnu.org/licenses/>.
##

