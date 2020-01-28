#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This files's authors include Max Neunhöffer.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
##
##  Handle the (projective) imprimitive, tensor and tensor-induced cases.
##  This file contains generic methods to find normal subgroups.
##
#############################################################################

DeclareInfoClass("InfoFindEvenNormal");
SetInfoLevel(InfoFindEvenNormal,0);

# DeclareGlobalFunction("RECOG_IsNormal");

# DeclareOperation( "FindEvenNormalSubgroup", [ IsGroup, IsRecord ] );
# DeclareOperation( "FindEvenNormalSubgroup", [ IsGroup ] );
DeclareOperation( "FindElmOfEvenNormalSubgroup", [ IsGroup, IsRecord ] );
DeclareOperation( "FindElmOfEvenNormalSubgroup", [ IsGroup ] );
