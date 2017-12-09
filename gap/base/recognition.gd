#############################################################################
##
##  recognition.gd        recog package
##                                                        Max Neunhoeffer
##                                                            Ákos Seress
##
##  Copyright 2005-2008 by the authors
##  This file is free software, see license information at the end.
##
##  Declaration stuff for generic recognition.
##
#############################################################################

# The category:
DeclareCategory( "IsRecognitionInfo", IsObject );
# The type:
DeclareGlobalVariable( "RecognitionInfoType" );
# The family:
BindGlobal( "RecognitionInfoFamily",
  NewFamily("RecognitionInfoFamily", IsRecognitionInfo));


# The info class:
DeclareInfoClass( "InfoRecog" );
SetInfoLevel(InfoRecog,1);

if IsBound(InfoSLP) then
    SetInfoLevel(InfoSLP,0);
fi;

# A place for package-local functions:
BindGlobal( "RECOG", rec() );

# Some properties and attributes of the recognition infos:
DeclareFilter( "IsLeaf" );
DeclareFilter( "IsReady" );
DeclareAttribute( "Grp", IsRecognitionInfo, "mutable" );
DeclareAttribute( "Homom", IsRecognitionInfo, "mutable" );
DeclareAttribute( "StdGens", IsRecognitionInfo, "mutable" );    # TODO: implement
DeclareAttribute( "NiceGens", IsRecognitionInfo, "mutable" );
DeclareAttribute( "RIFac", IsRecognitionInfo, "mutable" );
DeclareAttribute( "RIKer", IsRecognitionInfo, "mutable" );
DeclareAttribute( "RIParent", IsRecognitionInfo, "mutable" );
DeclareAttribute( "StdPresentation", IsRecognitionInfo, "mutable" );    # TODO: implement
DeclareProperty( "IsSimpleGroup", IsRecognitionInfo );
DeclareProperty( "IsAlmostSimpleGroup", IsRecognitionInfo );
InstallTrueMethod( IsAlmostSimpleGroup, IsSimpleGroup );

DeclareAttribute( "pregensfac", IsRecognitionInfo, "mutable" );
DeclareAttribute( "calcnicegens", IsRecognitionInfo, "mutable" );
DeclareAttribute( "slptonice", IsRecognitionInfo, "mutable" );
DeclareAttribute( "slptostd", IsRecognitionInfo, "mutable" );
DeclareAttribute( "fhmethsel", IsRecognitionInfo, "mutable" );      # TODO: rename?
DeclareAttribute( "methodsforfactor", IsRecognitionInfo, "mutable" ); # rename to MethodsDBForFactor
DeclareAttribute( "slpforelement", IsRecognitionInfo, "mutable" );
# Here we collect generators of the kernel:
DeclareAttribute( "gensN", IsRecognitionInfo, "mutable" );      # TODO: rename?
# The following holds a method, described by a record, to find generators
# of the kernel:
DeclareAttribute( "findgensNmeth", IsRecognitionInfo, "mutable" );
# Here is one slp to make all the gensN:
DeclareAttribute( "gensNslp", IsRecognitionInfo, "mutable" );
# Do we have to do an immediate verification of the kernel?
DeclareAttribute( "immediateverification", IsRecognitionInfo, "mutable" );
# Used to transport information about the group down to the kernel:
DeclareAttribute( "forkernel", IsRecognitionInfo, "mutable" );
# Used to transport information about the group down to the factor:
DeclareAttribute( "forfactor", IsRecognitionInfo, "mutable" );
# Used to check whether group elements are equal to one after recognition:
DeclareAttribute( "isone", IsRecognitionInfo, "mutable" );
# Used to compare group elements after recognition:
DeclareAttribute( "isequal", IsRecognitionInfo, "mutable" );



#############################################################################
# Some variables to hold databases of methods and such things:
#############################################################################

BindGlobal( "FindHomMethodsPerm", rec() );
BindGlobal( "SLPforElementFuncsPerm", rec() );
BindGlobal( "FindHomDbPerm", [] );

BindGlobal( "FindHomMethodsMatrix", rec() );
BindGlobal( "SLPforElementFuncsMatrix", rec() );
BindGlobal( "FindHomDbMatrix", [] );

BindGlobal( "FindHomMethodsProjective", rec() );
BindGlobal( "SLPforElementFuncsProjective", rec() );
BindGlobal( "FindHomDbProjective", [] );

BindGlobal( "FindHomMethodsBB", rec() );
BindGlobal( "SLPforElementFuncsBB", rec() );
BindGlobal( "FindHomDbBB", [] );


# Our global functions for the main recursion:

DeclareGlobalFunction( "EmptyRecognitionInfoRecord" );

DeclareGlobalFunction( "RecognisePermGroup" );
DeclareSynonym("RecognizePermGroup", RecognisePermGroup);
DeclareGlobalFunction( "RecogniseMatrixGroup" );
DeclareSynonym("RecognizeMatrixGroup", RecogniseMatrixGroup);
DeclareGlobalFunction( "RecogniseProjectiveGroup" );
DeclareSynonym("RecognizeProjectiveGroup", RecogniseProjectiveGroup);
DeclareGlobalFunction( "RecogniseBBGroup" );
DeclareSynonym("RecognizeBBGroup", RecogniseBBGroup);
DeclareGlobalFunction( "RecogniseGroup" );
DeclareSynonym("RecognizeGroup", RecogniseGroup);
DeclareGlobalFunction( "RecogniseGeneric" );
DeclareSynonym("RecognizeGeneric", RecogniseGeneric);
DeclareGlobalFunction( "PrintTreePos" );
DeclareGlobalFunction( "TryFindHomMethod" );

# Helper functions for the generic part:

DeclareGlobalFunction( "CalcNiceGens" );
DeclareGlobalFunction( "CalcNiceGensGeneric" );
DeclareGlobalFunction( "CalcNiceGensHomNode" );
DeclareGlobalFunction( "SLPforElementGeneric" );
DeclareGlobalFunction( "SLPforElement" );
DeclareGlobalFunction( "RandomSubproduct" );
DeclareGlobalFunction( "FastNormalClosure" );
DeclareGlobalFunction( "FindKernelFastNormalClosure" );
DeclareGlobalFunction( "FindKernelRandom" );
DeclareGlobalFunction( "FindKernelDoNothing" );
DeclareOperation( "RandomElm", [ IsRecognitionInfo, IsString, IsBool ] );
DeclareOperation( "RandomElmOrd", [ IsRecognitionInfo, IsString, IsBool ] );
DeclareOperation( "RandomElmPpd", [ IsRecognitionInfo, IsString, IsBool ] );
DeclareOperation( "RandomOrdersSeen", [ IsRecognitionInfo ] );
DeclareOperation( "StopStoringRandEls", [ IsRecognitionInfo ] );
DeclareOperation( "GetElmOrd", [ IsRecognitionInfo, IsRecord ] );
DeclareOperation( "GetElmPpd", [ IsRecognitionInfo, IsRecord ] );



# Finally the generic verification procedure:

DeclareGlobalFunction( "VerifyPermGroup" );
DeclareGlobalFunction( "VerifyMatrixGroup" );
DeclareGlobalFunction( "VerifyProjectiveGroup" );
DeclareGlobalFunction( "VerifyBBGroup" );
DeclareGlobalFunction( "VerifyGroup" );

# Some more user functions:

DeclareGlobalFunction( "DisplayCompositionFactors" );
DeclareGlobalFunction( "GetCompositionTreeNode" );

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

