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

DeclareGlobalVariable("FINDNORMALOPTS");

DeclareGlobalFunction("RECOG_EqProjective");
DeclareGlobalFunction("RECOG_IsNormal");

DeclareOperation( "FindEvenNormalSubgroup", [ IsGroup, IsRecord ] );
DeclareOperation( "FindEvenNormalSubgroup", [ IsGroup ] );

