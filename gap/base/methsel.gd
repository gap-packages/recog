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
## <Func Name="AddMethod" Arg="methodDb, method, rank"/>
## <Description>
#  Add the recognition method <A>method</A> with rank <A>rank</A> to the
#  method database <A>methodDb</A>. Return nothing.
#  <A>method</A> is inserted into <A>methodDb</A> such that the ranks of its
#  entries are in decreasing order.
#  For information on recognition methods and method databases see
#  <Ref Func="RecogMethod"/>
#  and Section <Ref Sect="methoddatabases"/>, respectively.
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
## The argument <A>db</A> must be a method database in the sense of
## Section <Ref Sect="methoddatabases"/>. <A>limit</A> must be a non-negative
## integer. <A>furtherargs</A> stands for an arbitrary number of additional
## arguments, which are handed down to the called methods. Of course they
## must fulfill the conventions defined for the methods in the database
## <A>db</A>.<P/>
## The function first creates a <Q>method selection</Q> record keeping track
## of the things that happened during the method trying procedure,
## which is also used during this procedure. Then it calls methods with
## the algorithm described below and in the end returns the method
## selection record in its final state.
## <P/>
## The method selection record has the following components:
## 
## <List>
##     <Mark><C>inapplicableMethods</C></Mark>
##     <Item>a record, in which for every method that returned <K>NeverApplicable</K>
##         the value 1 is bound to the component with name the stamp
##         of the method.</Item>
##     <Mark><C>failedMethods</C></Mark>
##     <Item>a record, in which for every time a method returned <K>TemporaryFailure</K>
##         the value bound to the component with name the stamp of the method
##         is increased by 1 (not being bound means zero).</Item>
##     <Mark><C>successMethod</C></Mark>
##     <Item>the stamp of the method that succeeded, if one did. This component
##         is only bound after successful completion.</Item>
##     <Mark><C>result</C></Mark>
##     <Item>a boolean value which is either <K>Success</K> or <K>TemporaryFailure</K>
##         depending on whether a successful method was found or the procedure
##         gave up respectively. This component is only bound after
##         completion of the method selection procedure.</Item>
##     <Mark><C>tolerance</C></Mark>
##     <Item>the number of times all methods failed until one succeeded. See
##         below.</Item>
## </List>
## 
## The algorithm used by <Ref Func="CallMethods"/> is extremely simple:
## It sets a counter <C>tolerance</C> to zero. The main loop starts at the
## beginning of the method database and runs through the methods in turn.
## Provided a method did not yet return <K>NeverApplicable</K> and did not yet return
## <K>TemporaryFailure</K> more than <C>tolerance</C> times before, it is tried. According
## to the value returned by the method, the following happens:
## 
## <List>
##     <Mark><K>NeverApplicable</K></Mark>
##     <Item>this is marked in the method selection record and the main
##           loop starts again at the beginning of the method database.</Item>
##     <Mark><K>TemporaryFailure</K></Mark>
##     <Item>this is counted in the method selection record and the main
##           loop starts again at the beginning of the method database.</Item>
##     <Mark><K>NotEnoughInformation</K></Mark>
##     <Item>the main loop goes to the next method in the method database.</Item>
##     <Mark><K>Success</K></Mark>
##     <Item>this is marked in the method selection record and the procedure
##           returns successfully.</Item>
## </List>
## 
## If the main loop reaches the end of the method database without calling
## a method (because all methods have already failed or are not applicable),
## then the counter <C>tolerance</C> is increased by one and everything
## starts all over again. This is repeated until <C>tolerance</C> is greater
## than the <C>limit</C> which is the second argument of
## <Ref Func="CallMethods"/>. The last value of the <C>tolerance</C> counter
## is returned in the component <C>tolerance</C> of the method selection
## record.<P/>
## 
## Note that the main loop starts again at the beginning of the method database
## after each failed method call! However, this does not lead to an infinite
## loop, because the failure is recorded in the method selection record such
## that the method is skipped until the <C>tolerance</C> increases. Once the
## <C>tolerance</C> has been increased methods having returned
## <K>TemporaryFailure</K> will be called again. The idea behind this approach is
## that even failed methods can collect additional information about the
## arguments changing them accordingly. This might give methods that come
## earlier and were not applicable up to now the opportunity to begin
## working. Therefore one can install very good methods that depend on some
## already known knowledge which will only be acquired during the method
## selection procedure by other methods, with a high rank.<P/>
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
BindGlobal("NotEnoughInformation", MakeImmutable("NotEnoughInformation"));
