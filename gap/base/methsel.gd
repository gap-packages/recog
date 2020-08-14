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

# InfoClass so that we can for example check whether every method checks
# whether its input is valid.
DeclareInfoClass( "InfoAddMethod" );
SetInfoLevel(InfoAddMethod, 0);

## <#GAPDoc Label="AddMethod">
## <ManSection>
## <Func Name="AddMethod" Arg="methodDb, method"/>
## <Returns>nothing</Returns>
## <Description>
#  <A>methodDb</A> must be a method database as in Section
#  <Ref Sect="whataremethods"/>.
#  <A>method</A> must be a record with the following components.
#  <A>method</A> is the method function,
#  <A>rank</A> the rank and <A>stamp</A> a string valued stamp, that is
#  <A>stamp</A> uniquely identifies the method among all other methods.
#  Optionally the component <A>comment</A> can be bound to a string.
#  <P/>
#  The method record <A>method</A> is inserted according to its rank, assuming
#  that the method database <A>methodDb</A> is in rank-descending order.
#  Nothing is returned.
## </Description>
## </ManSection>
## <#/GAPDoc>
DeclareGlobalFunction( "AddMethod" );

## <#GAPDoc Label="CallMethods">
## <ManSection>
## <Func Name="CallMethods" Arg="db, limit [,furtherargs]"/>
## <Returns>a record <C>ms</C> describing this method selection procedure.
## </Returns>
## <Description>
##     The argument <A>db</A> must be a method database in the sense of
##     Section <Ref Sect="whataremethods"/>. <A>limit</A> must be a non-negative
##     integer. <A>furtherargs</A> stands for an arbitrary number of additional
##     arguments, which are handed down to the called methods. Of course they
##     must fulfill the conventions defined for the methods in the database
##     <A>db</A>.<P/>
##     The function first creates a <Q>method selection</Q> record keeping track
##     of the things that happened during the method trying procedure,
##     which is also used during this procedure. Then it calls methods with
##     the algorithm described below and in the end returns the method
##     selection record in its final state.
## </Description>
## </ManSection>
## <#/GAPDoc>
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
