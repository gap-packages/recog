#############################################################################
##
##  methsel.gd          recog package
##                                                        Max Neunhoeffer
##                                                            Ákos Seress
##
##  Copyright 2005-2008 by the authors.
##  This file is free software, see license information at the end.
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
# method successfully computed a homomorphism
# (used to be 'true')
#BindGlobal("Success", MakeImmutable("Success"));
BindGlobal("Success", true);    # HACK: use old value for now, to ease transition

# method is never applicable to this kind of group (e.g. input is
# non-solvable, but method is only applicable to solvable groups),
# don't bother to try it again
# (used to be 'false')
#BindGlobal("NeverApplicable", MakeImmutable("NeverApplicable"));
BindGlobal("NeverApplicable", false);    # HACK: use old value for now, to ease transition

# The method temporarily failed, that it could be sensible to call it
# again in this situation at a later stage. This value is typical for a Las
# Vegas algorithm using randomised methods, which has failed, but which may
# succeed when called again.
# (used to be 'fail')
#BindGlobal("TemporaryFailure", MakeImmutable("TemporaryFailure"));
BindGlobal("TemporaryFailure", fail);    # HACK: use old value for now, to ease transition

# method needs more information (e.g. things like whether group is
# solvable; transitive; etc.) -> try again later if new information
# becomes available
# (used to be 'NotApplicable')
BindGlobal("NotEnoughInformation", "NotEnoughInformation");


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
