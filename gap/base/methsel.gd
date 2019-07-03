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
##  Declaration stuff for our own method selection.
##
#############################################################################

# Our own method selection code:

DeclareInfoClass( "InfoMethSel" );
SetInfoLevel(InfoMethSel,1);
DeclareGlobalFunction( "AddMethod" );
DeclareGlobalFunction( "CallMethods" );


# Possible return values for recognition methods:
#
# The method successfully computed a homomorphism (used to be 'true').
#BindGlobal("Success", MakeImmutable("Success"));
BindGlobal("Success", true);    # HACK: use old value for now, to ease transition

# The method is never applicable to this kind of group (e.g. input is
# non-solvable, but method is only applicable to solvable groups; or method
# only applies to permutation groups, but input is a matrix group). so don't
# bother to try it again (used to be 'false').
#BindGlobal("NeverApplicable", MakeImmutable("NeverApplicable"));
BindGlobal("NeverApplicable", false);    # HACK: use old value for now, to ease transition

# The method temporarily failed, but it could be sensible to call it again in
# this situation at a later stage. This value is typical for a Las Vegas
# algorithm using randomised methods, which has failed, but which may succeed
# when called again (used to be 'fail').
#BindGlobal("TemporaryFailure", MakeImmutable("TemporaryFailure"));
BindGlobal("TemporaryFailure", fail);    # HACK: use old value for now, to ease transition

# The method needs more information (e.g. things like whether group is
# solvable; transitive; etc.) -> try again later if new information becomes
# available (used to be 'NotApplicable').
BindGlobal("NotEnoughInformation", "NotEnoughInformation");
