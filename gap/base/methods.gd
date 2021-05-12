#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This files's authors include Sergio Siccha.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
##
##  Declarations of recog methods
##
#############################################################################

# <#GAPDoc Label="IsRecogMethod">
# <ManSection>
# <Filt Name="IsRecogMethod" Type="Category"/>
# <Description>
# The category of recognition methods, that is of the objects created via
# <Ref Func="RecogMethod"/>.
# </Description>
# </ManSection>
# <#/GAPDoc>
DeclareCategory("IsRecogMethod", IsObject);
BindGlobal("RecogMethodFamily", NewFamily("RecogMethodFamily", IsRecogMethod));
BindGlobal("RecogMethodType",
           NewType(RecogMethodFamily,
                   IsRecogMethod and IsAttributeStoringRep));

# <#GAPDoc Label="RecogMethod">
# <ManSection>
# <Func Name="RecogMethod" Arg="stamp, comment, func"/>
# <Description>
# Return a recognition method <C>method</C> in the filter
# <Ref Filt="IsRecogMethod"/>,
# where <A>stamp</A> is a string describing the method uniquely,
# <A>comment</A> is a string explaining how the method works, and
# <A>func</A> is the method itself.
# The components <A>stamp</A> and <A>comment</A> can be accessed via the
# attributes <Ref Attr="Stamp"/> and <Ref Attr="Comment"/>.
# <P/>
# A recognition method returns one of the following four values:
# <List>
# <Mark><K>Success</K></Mark>
# <Item>means that the method was successful and no more methods have to be
#     tried.</Item>
# <Mark><K>NeverApplicable</K></Mark>
# <Item>means that the method was not successful and that there is no point
#     to call the method again in this situation whatsoever.</Item>
# <Mark><K>TemporaryFailure</K></Mark>
# <Item>means that the method temporarily failed, that it however could be
#     sensible to call it again in this situation at a later stage. This
#     value is typical for a Las Vegas algorithm using randomised methods,
#     which has failed, but which may succeed when called again.</Item>
# <Mark><K>NotEnoughInformation</K></Mark>
# <Item>means that the method for some reason refused to do its work. However,
#     it is possible that it will become applicable later such that it makes
#     sense to call it again, for example when more information is available.</Item>
# </List>
# A recognition method <C>method</C> should always be stored into the component
# <C>Stamp(method)</C> of one of the following records:
# <Ref Var="FindHomMethodsGeneric"/>,
# <Ref Var="FindHomMethodsPerm"/>,
# <Ref Var="FindHomMethodsMatrix"/>, and
# <Ref Var="FindHomMethodsProjective"/>.
# To this end one can use the function <Ref Func="BindRecogMethod"/>.
# </Description>
# </ManSection>
# <#/GAPDoc>
DeclareGlobalFunction("RecogMethod");

# <#GAPDoc Label="BindRecogMethod">
# <ManSection>
# <Func Name="BindRecogMethod" Arg="r, arg"/>
# <Description>
# Create the recognition method <C>method</C> by calling
# <Ref Func="RecogMethod"/> with arguments <A>arg</A>.
# Then bind the component <C>Stamp(method)</C> of <A>r</A> to <A>method</A>.
# </Description>
# </ManSection>
# <#/GAPDoc>
DeclareGlobalFunction("BindRecogMethod");

# <#GAPDoc Label="CallRecogMethod">
# <ManSection>
# <Func Name="CallRecogMethod" Arg="m, args"/>
# <Description>
# Call <C>UnpackRecogMethod(m)</C> with arguments <A>args</A> and return the
# return value.
# The argument <A>m</A> must lie in <Ref Filt="IsRecogMethod"/>.
# </Description>
# </ManSection>
# <#/GAPDoc>
DeclareGlobalFunction("CallRecogMethod");

# <#GAPDoc Label="Stamp">
# <ManSection>
# <Attr Name="Stamp" Arg="method"/>
# <Description>
# The stamp of <A>method</A>, see <Ref Func="RecogMethod"/>.
# The argument <A>method</A> must lie in <Ref Filt="IsRecogMethod"/>.
# </Description>
# </ManSection>
# <#/GAPDoc>
DeclareAttribute("Stamp", IsRecogMethod);

# <#GAPDoc Label="Comment">
# <ManSection>
# <Attr Name="Comment" Arg="method"/>
# <Description>
# The comment of <A>method</A>, see <Ref Func="RecogMethod"/>.
# The argument <A>method</A> must lie in <Ref Filt="IsRecogMethod"/>.
# </Description>
# </ManSection>
# <#/GAPDoc>
DeclareAttribute("Comment", IsRecogMethod);
DeclareAttribute("ValidatesOrAlwaysValidInput", IsRecogMethod);
