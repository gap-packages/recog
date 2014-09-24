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

PACKAGE := "recog";
SetPackagePath(PACKAGE, ".");
PrintTo("VERSION", PackageInfo(PACKAGE)[1].Version);

LoadPackage("GAPDoc");
LoadPackage("recogbase");

if fail <> LoadPackage("AutoDoc", ">= 2014.03.27") then
    AutoDoc(PACKAGE : scaffold := rec( MainPage := false ));
else
    MakeGAPDocDoc("doc", PACKAGE, [], PACKAGE, "MathJax");
    CopyHTMLStyleFiles("doc");
    GAPDocManualLab(PACKAGE);
fi;

QUIT;

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

