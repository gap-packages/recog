#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This files's authors include Max Neunhöffer, Ákos Seress.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
##
##  Code to recognise (simple) groups by their two largest element orders.
##  At least recognise the "natural" characteristic.
##
#############################################################################

DeclareGlobalFunction( "InstallAlmostSimpleHint" );
DeclareGlobalFunction( "DoHintedLowIndex" );
DeclareGlobalFunction( "DoHintedStabChain" );
DeclareGlobalFunction( "LookupHintForSimple" );
