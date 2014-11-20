#############################################################################
##
##  read.g                recogbase package
##                                                        Max Neunhoeffer
##                                                            Ákos Seress
##
##  Copyright 2005-2008 by the authors.
##  This file is free software, see license information at the end.
##
##  Reading the implementation part of the recogbase package.
##
#############################################################################

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

