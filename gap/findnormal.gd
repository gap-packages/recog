#############################################################################
##
##  findnormal.gd          
##                                recog package  
##                                                        Max Neunhoeffer
##
##  Copyright 2009 by the authors.
##  This file is free software, see license information at the end.
##
##  Handle the (projective) imprimitive, tensor and tensor-induced cases.
##  This file contains generic methods to find normal subgroups.
##
#############################################################################

DeclareInfoClass("InfoFindEvenNormal");
SetInfoLevel(InfoFindEvenNormal,0);

DeclareGlobalVariable("FINDEVENNORMALOPTS");

DeclareGlobalFunction("RECOG_EqProjective");
DeclareGlobalFunction("RECOG_IsNormal");

DeclareOperation( "FindEvenNormalSubgroup", [ IsGroup, IsRecord ] );
DeclareOperation( "FindEvenNormalSubgroup", [ IsGroup ] );
DeclareOperation( "FindElmOfEvenNormalSubgroup", [ IsGroup, IsRecord ] );
DeclareOperation( "FindElmOfEvenNormalSubgroup", [ IsGroup ] );

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
