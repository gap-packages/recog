#############################################################################
##
##  makedoc.g
##                              recog package                   
##                                                        Max Neunhoeffer
##                                                            Ákos Seress
##                                                                 et al.
##
##  Copyright 2005-2008 by the authors.
##  This file is free software, see license information at the end.
##
##  this creates the documentation, needs: GAPDoc package, latex, pdflatex,
##  mkindex, dvips, recogbase package
##  
##  Call this with GAP.
##
##
#############################################################################

LoadPackage("GAPDoc");
LoadPackage("recogbase");

MakeGAPDocDoc("doc", "recog", [], "recog");

GAPDocManualLab("recog");

quit;

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

