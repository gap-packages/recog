#############################################################################
##
##  slptools.gd        recog package                      Max Neunhoeffer
##                                                            Ákos Seress
##
##  Copyright 2005 Lehrstuhl D für Mathematik, RWTH Aachen
##  This file is free software, see license information at the end.
##
##  Some additional things for straight line programs.
##
#############################################################################


# The following will be documented soon:

DeclareGlobalFunction( "SLPChangesSlots" );
DeclareGlobalFunction( "SLPOnlyNeededLinesBackward" );
DeclareGlobalFunction( "SLPReversedRenumbered" );
DeclareGlobalFunction( "RestrictOutputsOfSLP" );
DeclareGlobalFunction( "IntermediateResultOfSLP" );
DeclareGlobalFunction( "IntermediateResultsOfSLPWithoutOverwriteInner" );
DeclareGlobalFunction( "IntermediateResultsOfSLPWithoutOverwrite" );
DeclareGlobalFunction( "IntermediateResultOfSLPWithoutOverwrite" );
DeclareGlobalFunction( "ProductOfStraightLinePrograms" );
DeclareGlobalFunction( "RewriteStraightLineProgram" );
DeclareGlobalFunction( "NewCompositionOfStraightLinePrograms" );
DeclareGlobalFunction( "NewProductOfStraightLinePrograms" );

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

