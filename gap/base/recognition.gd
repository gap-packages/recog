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

## <#GAPDoc Label="IsLeaf">
## <ManSection>
## <Filt Name="IsLeaf" Type="Flag"/>
## <Description>
## This flag indicates, whether or not a recognition info record represents a leaf
## in the recognition tree. If it is not set, one finds at least one of
## the attributes <Ref Attr="RIFac"/> and <Ref Attr="RIKer"/> set for
## the corresponding node. This flag is normally reset and has to be set
## by a find homomorphism method to indicate a leaf.
## </Description>
## </ManSection>
## <#/GAPDoc>
DeclareFilter( "IsLeaf" );

## <#GAPDoc Label="IsReady">
## <ManSection>
## <Filt Name="IsReady" Type="Flag"/>
## <Description>
## This flag indicates during the recognition procedure, whether a node in
## the recognition tree is already completed or not. It is mainly set for
## debugging purposes during the recognition. However, if the recognition
## fails somewhere in a leaf, this flag is not set and all nodes above will
## also not have this flag set. In this way one can see whether the recognition
## failed and where the problem was.
## </Description>
## </ManSection>
## <#/GAPDoc>
DeclareFilter( "IsReady" );

## <#GAPDoc Label="Grp">
## <ManSection>
## <Attr Name="Grp" Arg="ri"/>
## <Description>
## The value of this attribute is the group that is to be recognised by this
## recognition info record <A>ri</A>. This attribute is always present during
## recognition and after completion. Note that the generators of the group
## object stored here always have a memory attached to them, such that
## elements that are generated from them remember, how they were acquired.
## </Description>
## </ManSection>
## <#/GAPDoc>
DeclareAttribute( "Grp", IsRecognitionInfo, "mutable" );

## <#GAPDoc Label="Homom">
## <ManSection>
## <Attr Name="Homom" Arg="ri"/>
## <Description>
##     The value of this attribute is the homomorphism that was found from the
##     group described by the recognition info record <A>ri</A> as a &GAP;
##     object. It is set by a find homomorphism method that succeeded to
##     find a homomorphism (or isomorphism). It does not have to be set
##     in leaf nodes of the recognition tree.
## </Description>
## </ManSection>
## <#/GAPDoc>
DeclareAttribute( "Homom", IsRecognitionInfo, "mutable" );

## <#GAPDoc Label="NiceGens">
## <ManSection>
## <Attr Name="NiceGens" Arg="ri"/>
## <Description>
##     The value of this attribute must be set for all nodes and contains
##     the nice generators. The <Ref Func="SLPforElement"/> function of the
##     node will write its straight line program in terms of these nice
##     generators. For leaf nodes, the find homomorphism method is responsible
##     to set the value of <Ref Attr="NiceGens"/>. By default, the original
##     generators of the group at this node are taken. For a homomorphism
##     (or isomorphism), the <Ref Attr="NiceGens"/> will be the concatenation
##     of preimages of the <Ref Attr="NiceGens"/> of the factor group
##     (see <Ref Attr="pregensfac"/>) and
##     the <Ref Attr="NiceGens"/> of the kernel. A find homomorphism method
##     does not have to set <Ref Attr="NiceGens"/> if it finds a homomorphism.
##     Note however, that such a find homomorphism method has to ensure somehow,
##     that preimages of the <Ref Attr="NiceGens"/> of the factor group
##     can be acquired. See <Ref Attr="calcnicegens"/>, <Ref Func="CalcNiceGens"/>
##     and <Ref Attr="slptonice"/>
##     for instructions.
## </Description>
## </ManSection>
## <#/GAPDoc>
DeclareAttribute( "NiceGens", IsRecognitionInfo, "mutable" );

## <#GAPDoc Label="RIFac">
## <ManSection>
## <Attr Name="RIFac" Arg="ri"/>
## <Description>
##     The value of this attribute is the recognition info record of the
##     image of the homomorphism that was found from the group described by
##     the recognition info record <A>ri</A>. It is set by the generic
##     recursive procedure after a find homomorphism method has succeeded
##     to find a homomorphism (or isomorphism). It does not have to be set
##     in leaf nodes of the recognition tree. This attribute value provides
##     the link to the <Q>factor</Q> subtree of the recognition tree.
## </Description>
## </ManSection>
## <#/GAPDoc>
DeclareAttribute( "RIFac", IsRecognitionInfo, "mutable" );

## <#GAPDoc Label="RIKer">
## <ManSection>
## <Attr Name="RIKer" Arg="ri"/>
## <Description>
##     The value of this attribute is the recognition info record of the
##     kernel of the homomorphism that was found from the group described by
##     the recognition info record <A>ri</A>. It is set by the generic
##     recursive procedure after a find homomorphism method has succeeded
##     to find a homomorphism (or isomorphism). It does not have to be set
##     in leaf nodes of the recognition tree or if the homomorphism is known to
##     be an isomorphism. In the latter case the value of the attribute is
##     set to <K>fail</K>. This attribute value provides the link to the
##     <Q>kernel</Q> subtree of the recognition tree.
## </Description>
## </ManSection>
## <#/GAPDoc>
DeclareAttribute( "RIKer", IsRecognitionInfo, "mutable" );

## <#GAPDoc Label="RIParent">
## <ManSection>
## <Attr Name="RIParent" Arg="ri"/>
## <Description>
##     The value of this attribute is the recognition info record of the
##     parent of this node in the recognition tree. The top node does not
##     have this attribute set.
## </Description>
## </ManSection>
## <#/GAPDoc>
DeclareAttribute( "RIParent", IsRecognitionInfo, "mutable" );

## <#GAPDoc Label="StdPresentation">
## <ManSection>
## <Attr Name="StdPresentation" Arg="ri"/>
## <Description>
##     After the verification phase, the presentation is stored here. Details
##     have still to be decided upon.
## </Description>
## </ManSection>
## <#/GAPDoc>
DeclareAttribute( "StdPresentation", IsRecognitionInfo, "mutable" );    # TODO: implement

DeclareProperty( "IsRecogInfoForSimpleGroup", IsRecognitionInfo );
DeclareProperty( "IsRecogInfoForAlmostSimpleGroup", IsRecognitionInfo );
InstallTrueMethod( IsRecogInfoForAlmostSimpleGroup, IsRecogInfoForSimpleGroup );

## <#GAPDoc Label="pregensfac">
## <ManSection>
## <Attr Name="pregensfac" Arg="ri"/>
## <Description>
##     The value of this attribute is only set for homomorphism nodes. In that
##     case it contains preimages of the nice generators in the factor group.
##     This attribute is set automatically by the generic recursive recognition
##     function using the mechanism described with the attribute
##     <Ref Attr="calcnicegens"/> below. A find homomorphism does not have
##     to touch this attribute.
## </Description>
## </ManSection>
## <#/GAPDoc>
DeclareAttribute( "pregensfac", IsRecognitionInfo, "mutable" );
DeclareAttribute( "validatehomominput", IsRecognitionInfo);

## <#GAPDoc Label="calcnicegens">
## <ManSection>
## <Attr Name="calcnicegens" Arg="ri"/>
## <Description>
##     To make the recursion work, we have to acquire preimages of the
##     nice generators in factor groups under the homomorphism found.
##     But we want to keep the information, how the nice generators
##     were found, locally at the node where they were found. This
##     attribute solves this problem of acquiring preimages in the following
##     way: Its value must be a function, taking the recognition info
##     record <A>ri</A> as first argument, and a list <A>origgens</A> of
##     preimages of the
##     original generators of the current node, and has to
##     return corresponding preimages of the nice generators. Usually this
##     task can be done by storing a straight line program writing the
##     nice generators in terms of the original generators and executing
##     this with inputs <A>origgens</A>. Therefore the default value of
##     this attribute is the function <Ref Func="CalcNiceGensGeneric"/>
##     described below.
## </Description>
## </ManSection>
## <#/GAPDoc>
DeclareAttribute( "calcnicegens", IsRecognitionInfo, "mutable" );

## <#GAPDoc Label="slptonice">
## <ManSection>
## <Attr Name="slptonice" Arg="ri"/>
## <Description>
##     As described above, the value, if set, must be a straight line program
##     expressing the nice generators at this node in terms of the original
##     generators. This is for leaf nodes, that choose to use the default
##     function <Ref Func="CalcNiceGensGeneric"/> installed in the
##     <Ref Attr="calcnicegens"/> attribute.
## </Description>
## </ManSection>
## <#/GAPDoc>
DeclareAttribute( "slptonice", IsRecognitionInfo, "mutable" );

## <#GAPDoc Label="fhmethsel">
## <ManSection>
## <Attr Name="fhmethsel" Arg="ri"/>
## <Description>
##     The value of this attribute is the record returned by the method
##     selection (see Section <Ref Sect="howcalled"/>) after it ran to
##     find a homomorphism (or isomorphism). It is there to be able to see
##     which methods were tried until the recognition of the node was
##     completed.
## </Description>
## </ManSection>
## <#/GAPDoc>
DeclareAttribute( "fhmethsel", IsRecognitionInfo, "mutable" );      # TODO: rename?

## <#GAPDoc Label="methodsforfactor">
## <ManSection>
## <Attr Name="methodsforfactor" Arg="ri"/>
## <Description>
##     This attribute is initialised at the beginning of the recursive
##     recognition function with the database of find homomorphism methods
##     that was used to recognise the group corresponding to the
##     recognition info record <A>ri</A>. If the found homomorphism
##     changes the representation of the group (going for example from
##     a matrix group to a permutation group), the find homomorphism method
##     can report this by exchanging the database of find homomorphism methods
##     to be used in the recognition of the image of the homomorphism by
##     setting the value of this attribute to something different. It lies
##     in the responsibility of the find homomorphism method to do so,
##     if the representation changes through the homomorphism.
## </Description>
## </ManSection>
## <#/GAPDoc>
DeclareAttribute( "methodsforfactor", IsRecognitionInfo, "mutable" ); # rename to MethodsDBForFactor

## <#GAPDoc Label="slpforelement">
## <ManSection>
## <Attr Name="slpforelement" Arg="ri"/>
## <Description>
##     After the recognition phase is completed for the node <A>ri</A>, we
##     are by definition able to write arbitrary elements in the group described
##     by this node as a straight line program (SLP) in terms of the nice
##     generators stored in <Ref Attr="NiceGens"/>.
##     This attribute value is a function taking the node <A>ri</A> and a
##     group element as its arguments and returning the above mentioned
##     straight line program. For the case that a find homomorphism method
##     succeeds in finding a homomorphism, the generic recursive function
##     sets this attribute to the function <Ref Func="SLPforElementGeneric"/>
##     which does the job for the generic homomorphism situation. In all other
##     cases the successful find homomorphism method has to set this attribute
##     to a function doing the job. The find homomorphism method is free to
##     store additional data in the recognition info record or the group
##     object such that the <Ref Func="SLPforElement"/> function can work.
## </Description>
## </ManSection>
## <#/GAPDoc>
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
# Used to compute order of group elements after recognition:
DeclareAttribute( "order", IsRecognitionInfo, "mutable" );



#############################################################################
# Some variables to hold databases of methods and such things:
#############################################################################

## <#GAPDoc Label="FindHomMethodsPerm">
## <ManSection>
## <Var Name="FindHomMethodsPerm"/>
## <Description>
##     In this global record the functions that are methods for finding
##     homomorphisms for permutation group recognition are stored. We
##     collect them all in this record such that we do not use up too many
##     global variable names.
## </Description>
## </ManSection>
## <#/GAPDoc>
DeclareGlobalVariable( "FindHomMethodsPerm" );

## <#GAPDoc Label="SLPforElementFuncsPerm">
## <ManSection>
## <Var Name="SLPforElementFuncsPerm"/>
## <Description>
##     This global record holds the functions that are methods for writing group
##     elements as straight line programs (SLPs) in terms of the generators
##     after successful permutation group recognition. We collect them all in this
##     record such that we do not use up too many global variable names.
## </Description>
## </ManSection>
## <#/GAPDoc>
DeclareGlobalVariable( "SLPforElementFuncsPerm" );

## <#GAPDoc Label="FindHomDbPerm">
## <ManSection>
## <Var Name="FindHomDbPerm"/>
## <Description>
##     This list contains the methods for finding homomorphisms
##     for permutation group recognition that are stored in the record
##     <Ref Var="FindHomMethodsPerm"/>. As described in Section <Ref
##     Sect="whataremethods"/> each method is described by a record. The list
##     is always sorted with respect to decreasing ranks. The order in this
##     list tells in which order the methods should be applied. Use <Ref
##     Func="AddMethod"/> to add methods to this database.
## </Description>
## </ManSection>
## <#/GAPDoc>
DeclareGlobalVariable( "FindHomDbPerm" );

## <#GAPDoc Label="FindHomMethodsMatrix">
## <ManSection>
## <Var Name="FindHomMethodsMatrix"/>
## <Description>
##     In this global record the functions that are methods for finding
##     homomorphisms for matrix group recognition are stored. We collect
##     them all in this record such that we do not use up too many global
##     variable names.
## </Description>
## </ManSection>
## <#/GAPDoc>
DeclareGlobalVariable( "FindHomMethodsMatrix" );

## <#GAPDoc Label="SLPforElementFuncsMatrix">
## <ManSection>
## <Var Name="SLPforElementFuncsMatrix"/>
## <Description>
##     This global record holds the functions that are methods for writing group
##     elements as straight line programs (SLPs) in terms of the generators
##     after successful matrix group recognition. We collect them all in this
##     record such that we do not use up too many global variable names.
## </Description>
## </ManSection>
## <#/GAPDoc>
DeclareGlobalVariable( "SLPforElementFuncsMatrix" );

## <#GAPDoc Label="FindHomDbMatrix">
## <ManSection>
## <Var Name="FindHomDbMatrix"/>
## <Description>
##     This list contains the methods for finding homomorphisms
##     for matrix group recognition that are stored in the record
##     <Ref Var="FindHomMethodsMatrix"/>. As described in Section <Ref
##     Sect="whataremethods"/> each method is described by a record. The list
##     is always sorted with respect to decreasing ranks. The order in this
##     list tells in which order the methods should be applied. Use <Ref
##     Func="AddMethod"/> to add methods to this database.
## </Description>
## </ManSection>
## <#/GAPDoc>
DeclareGlobalVariable( "FindHomDbMatrix" );

## <#GAPDoc Label="FindHomMethodsProjective">
## <ManSection>
## <Var Name="FindHomMethodsProjective"/>
## <Description>
##     In this global record the functions that are methods for finding
##     homomorphisms for projective group recognition are stored. We collect
##     them all in this record such that we do not use up too many global
##     variable names.
## </Description>
## </ManSection>
## <#/GAPDoc>
DeclareGlobalVariable( "FindHomMethodsProjective" );

## <#GAPDoc Label="SLPforElementFuncsProjective">
## <ManSection>
## <Var Name="SLPforElementFuncsProjective"/>
## <Description>
##     This global record holds the functions that are methods for writing group
##     elements as straight line programs (SLPs) in terms of the generators
##     after successful projective group recognition. We collect them all in this
##     record such that we do not use up too many global variable names.
## </Description>
## </ManSection>
## <#/GAPDoc>
DeclareGlobalVariable( "SLPforElementFuncsProjective" );

## <#GAPDoc Label="FindHomDbProjective">
## <ManSection>
## <Var Name="FindHomDbProjective"/>
## <Description>
##     This list contains the methods for finding homomorphisms
##     for projective group recognition that are stored in the record
##     <Ref Var="FindHomMethodsProjective"/>. As described in Section <Ref
##     Sect="whataremethods"/> each method is described by a record. The list
##     is always sorted with respect to decreasing ranks. The order in this
##     list tells in which order the methods should be applied. Use <Ref
##     Func="AddMethod"/> to add methods to this database.
## </Description>
## </ManSection>
## <#/GAPDoc>
DeclareGlobalVariable( "FindHomDbProjective" );

## <#GAPDoc Label="FindHomMethodsGeneric">
## <ManSection>
## <Var Name="FindHomMethodsGeneric"/>
## <Description>
##     In this global record the functions that are methods for finding
##     homomorphisms for generic group recognition are stored. We
##     collect them all in this record such that we do not use up too many
##     global variable names.
## </Description>
## </ManSection>
## <#/GAPDoc>
DeclareGlobalVariable( "FindHomMethodsGeneric" );

## <#GAPDoc Label="SLPforElementFuncsGeneric">
## <ManSection>
## <Var Name="SLPforElementFuncsGeneric"/>
## <Description>
##     This global record holds the functions that are methods for writing group
##     elements as straight line programs (SLPs) in terms of the generators
##     after successful generic group recognition. We collect them all in this
##     record such that we do not use up too many global variable names.
## </Description>
## </ManSection>
## <#/GAPDoc>
DeclareGlobalVariable( "SLPforElementFuncsGeneric" );


# Our global functions for the main recursion:

DeclareGlobalFunction( "EmptyRecognitionInfoRecord" );

## <#GAPDoc Label="RecognisePermGroup">
## <ManSection>
## <Func Name="RecognisePermGroup" Arg="H"/>
## <Func Name="RecognizePermGroup" Arg="H"/>
## <Returns><K>fail</K> for failure or a recognition info record.</Returns>
## <Description>
## <A>H</A> must be a &GAP; permutation group object. This function calls
## <Ref Func="RecogniseGeneric"/> with the method database used for
## permutation groups, which is stored in the global variable
## <Ref Var="FindHomDbPerm"/>, and no prior knowledge.
## </Description>
## </ManSection>
## <#/GAPDoc>
DeclareGlobalFunction( "RecognisePermGroup" );
DeclareSynonym("RecognizePermGroup", RecognisePermGroup);

## <#GAPDoc Label="RecogniseMatrixGroup">
## <ManSection>
## <Func Name="RecogniseMatrixGroup" Arg="H"/>
## <Func Name="RecognizeMatrixGroup" Arg="H"/>
## <Returns><K>fail</K> for failure or a recognition info record.</Returns>
## <Description>
## <A>H</A> must be a &GAP; matrix group object. This function calls
## <Ref Func="RecogniseGeneric"/> with the method database used for
## matrix groups, which is stored in the global variable
## <Ref Var="FindHomDbMatrix"/>, and no prior knowledge.
## </Description>
## </ManSection>
## <#/GAPDoc>
DeclareGlobalFunction( "RecogniseMatrixGroup" );
DeclareSynonym("RecognizeMatrixGroup", RecogniseMatrixGroup);

## <#GAPDoc Label="RecogniseProjectiveGroup">
## <ManSection>
## <Func Name="RecogniseProjectiveGroup" Arg="H"/>
## <Func Name="RecognizeProjectiveGroup" Arg="H"/>
## <Returns><K>fail</K> for failure or a recognition info record.</Returns>
## <Description>
## <A>H</A> must be a &GAP; matrix group object. Since as of now no
## actual projective groups are implemented in the &GAP; library we use
## matrix groups instead. The recognition will however view the group as
## the projective group, i.e. the matrix group modulo its scalar
## matrices. This function calls
## <Ref Func="RecogniseGeneric"/> with the method database used for
## projective groups, which is stored in the global variable
## <Ref Var="FindHomDbProjective"/>, and no prior knowledge.
## </Description>
## </ManSection>
## <#/GAPDoc>
DeclareGlobalFunction( "RecogniseProjectiveGroup" );
DeclareSynonym("RecognizeProjectiveGroup", RecogniseProjectiveGroup);

## <#GAPDoc Label="RecogniseGroup">
## <ManSection>
## <Func Name="RecogniseGroup" Arg="H"/>
## <Func Name="RecognizeGroup" Arg="H"/>
## <Returns><K>fail</K> for failure or a recognition info record.</Returns>
## <Description>
##     <A>H</A> must be a &GAP; group object. This function automatically
##     dispatches to one of the two previous functions
##     <Ref Func="RecognisePermGroup"/>, or <Ref Func="RecogniseMatrixGroup"/>,
##     according to the type of the group <A>H</A>.
##     Note that since currently there is no implementation of projective
##     groups in the &GAP; library, one cannot recognise a matrix group
##     <A>H</A> as a projective group using this function.
## </Description>
## </ManSection>
## <#/GAPDoc>
DeclareGlobalFunction( "RecogniseGroup" );
DeclareSynonym("RecognizeGroup", RecogniseGroup);

## <#GAPDoc Label="RecogniseGeneric">
## <ManSection>
## <Func Name="RecogniseGeneric" Arg="H, methoddb, depthString, knowledge"/>
## <Func Name="RecognizeGeneric" Arg="H, methoddb, depthString, knowledge"/>
## <Returns><K>fail</K> for failure or a recognition info record.</Returns>
## <Description>
##     <A>H</A> must be a &GAP; group object, <A>methoddb</A> must be a
##     method database in the sense of Section <Ref Sect="whataremethods"/>
##     containing <C>FindHomomorphism</C> methods in the sense of Section
##     <Ref Sect="findhomo"/>. <A>depthString</A> is a string whose length
##     measures the depth in the recognition tree. It will be increased by one
##     character for each step we go into the tree, namely by <C>F</C> for
##     a factor node, and <C>K</C> for a kernel. The top level begins with an
##     empty string. <A>knowledge</A> is an optional record the
##     components of which are copied into the new recognition info record
##     which is created for the group <A>H</A>. Especially the component
##     <C>hints</C> can contain a list of additional find homomorphism
##     methods (described by records as in Section <Ref Sect="whataremethods"/>)
##     which is prepended to the method database in <A>methoddb</A> before
##     the recognition starts. This feature is intended to give hints
##     about prior knowledge about which find homomorphism method might succeed.
##     <P/>
##     The function performs the algorithm described above and returns either
##     <K>fail</K> in case of failure or a recognition info record in case
##     of success. For the content and definition of recognition info
##     records see Section <Ref Sect="rirecord"/>.
## </Description>
## </ManSection>
## <#/GAPDoc>
DeclareGlobalFunction( "RecogniseGeneric" );
DeclareSynonym("RecognizeGeneric", RecogniseGeneric);

DeclareGlobalFunction( "PrintTreePos" );
DeclareGlobalFunction( "TryFindHomMethod" );

# Helper functions for the generic part:

## <#GAPDoc Label="CalcNiceGens">
## <ManSection>
## <Func Name="CalcNiceGens" Arg="ri, origgens"/>
## <Returns>a list of preimages of the nice generators</Returns>
## <Description>
##     This is a wrapper function which extracts the value of the attribute
##     <Ref Attr="calcnicegens"/> and calls that function with the arguments
##     <A>ri</A> and <A>origgens</A>.
## </Description>
## </ManSection>
## <#/GAPDoc>
DeclareGlobalFunction( "CalcNiceGens" );
DeclareGlobalFunction( "ValidateHomomInput" );

## <#GAPDoc Label="CalcNiceGensGeneric">
## <ManSection>
## <Func Name="CalcNiceGensGeneric" Arg="ri, origgens"/>
## <Returns>a list of preimages of the nice generators</Returns>
## <Description>
##     This is the default function for leaf nodes for the attribute <Ref
##     Attr="calcnicegens"/> described above. It does the following: If the
##     value of the attribute <Ref Attr="slptonice"/> is set, then it must
##     be a straight line program expressing the nice generators in terms
##     of the original generators of this node. In that case, this straight
##     line program is executed with <A>origgens</A> as inputs and the
##     result is returned. Otherwise, <A>origgens</A> is returned as is.
##     Therefore a leaf node just has to do nothing if the nice generators
##     are equal to the original generators, or can simply store the right
##     straight line program into the attribute <Ref Attr="slptonice"/> to
##     fulfill its duties.
## </Description>
## </ManSection>
## <#/GAPDoc>
DeclareGlobalFunction( "CalcNiceGensGeneric" );

## <#GAPDoc Label="CalcNiceGensHomNode">
## <ManSection>
## <Func Name="CalcNiceGensHomNode" Arg="ri, origgens"/>
## <Returns>a list of preimages of the nice generators</Returns>
## <Description>
##     This is the default function for homomorphism node for the attribute
##     <Ref Attr="calcnicegens"/>. It just delegates to factor and kernel of
##     the homomorphism, as the nice generators of a homomorphism (or isomorphism)
##     node are just the concatenation of the nice generators of the factor
##     and the kernel. A find homomorphism method finding a homomorphism
##     or isomorphism does not have to do anything with respect to nice
##     generators.
## </Description>
## </ManSection>
## <#/GAPDoc>
DeclareGlobalFunction( "CalcNiceGensHomNode" );
DeclareGlobalFunction( "SLPforElementGeneric" );

## <#GAPDoc Label="SLPforElement">
## <ManSection>
## <Func Name="SLPforElement" Arg="ri, x"/>
## <Returns>a straight line program expressing <A>x</A> in the nice generators.
## </Returns>
## <Description>
##     This is a wrapper function which extracts the value of the attribute
##     <Ref Attr="slpforelement"/> and calls that function with the arguments
##     <A>ri</A> and <A>x</A>.
## </Description>
## </ManSection>
## <#/GAPDoc>
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
DeclareGlobalFunction( "VerifyGroup" );

# Some more user functions:

## <#GAPDoc Label="DisplayCompositionFactors">
## <ManSection>
## <Func Name="DisplayCompositionFactors" Arg="ri"/>
## <Returns>nothing</Returns>
## <Description>
##     This function displays a composition series by using the recursive
##     recognition tree. It only works, if the usual operation
##     <Ref Oper="CompositionSeries" BookName="ref"/> works for all
##     leaves. THIS DOES CURRENTLY NOT WORK FOR PROJECTIVE GROUPS AND
##     THUS FOR MATRIX GROUPS!
## </Description>
## </ManSection>
## <#/GAPDoc>
DeclareGlobalFunction( "DisplayCompositionFactors" );

## <#GAPDoc Label="SLPforNiceGens">
## <ManSection>
## <Func Name="SLPforNiceGens" Arg="ri"/>
## <Returns>an SLP expressing the nice generators in the original ones</Returns>
## <Description>
##     This function assembles a possibly quite large straight line program
##     expressing the nice generators in terms of the original ones by using
##     the locally stored information in the recognition tree recursively.<P/>
##     You can concatenate straight line programs in the nice generators with
##     the result of this function to explicitly write an element in terms
##     of the original generators.
## </Description>
## </ManSection>
## <#/GAPDoc>
DeclareGlobalFunction( "SLPforNiceGens" );

DeclareGlobalFunction( "GetCompositionTreeNode" );
