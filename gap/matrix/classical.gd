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
##  The classical groups recognition.
##
#############################################################################

DeclareInfoClass( "InfoClassical" );
SetInfoLevel(InfoClassical,1);

## <#GAPDoc Label="RecogniseClassical">
## <ManSection>
## <Func Name="RecogniseClassical" Arg="grp[, opt]"/>
## <Returns>
## a record describing the outcome of the non-constructive recognition
## procedure.
## </Returns>
## <Description>
## This function implements non-constructive recognition, also called naming,
## for classical groups in their natural matrix representation over finite
## fields. The implementation is based on the algorithms described in
## <Cite Key="NP98"/>, <Cite Key="NP97"/>, and <Cite Key="NP99"/>, and uses
## further ingredients from <Cite Key="CLG97a"/>, <Cite Key="CLG97b"/>, and
## <Cite Key="Pra99"/>.
## <P/>
## The input <A>grp</A> must be a matrix group over a finite field. The
## function is intended for groups that are classical, or close to classical,
## in their natural representation.
## <P/>
## The optional record <A>opt</A> can be used to guide the computation. Its
## component <C>case</C> may be one of <C>"unknown"</C>, <C>"linear"</C>,
## <C>"symplectic"</C>, <C>"unitary"</C>, <C>"orthogonalplus"</C>, or
## <C>"orthogonalcircle"</C>. Furthermore, <C>nrrandels</C> controls how many
## random elements are inspected, and <C>infoLevel</C> sets the
## <C>InfoMethSel</C> level used while running the method selection
## machinery.
## <P/>
## The returned record is currently mostly an internal data structure and its
## full set of components should not be considered a stable public interface.
## The most useful documented components are the booleans <C>isReducible</C>,
## <C>isSLContained</C>, <C>isSpContained</C>, <C>isSUContained</C>, and
## <C>isOmegaContained</C>. The four <C>is*Contained</C> components indicate
## whether the given group contains the corresponding quasisimple classical
## group in the natural representation, namely <M>SL(d,q)</M>,
## <M>Sp(d,q)</M>, <M>SU(d,q)</M>, and <M>\Omega</M> of the appropriate type.
## <P/>
## To inspect the full internal record for debugging purposes, use
## <Ref Func="DisplayRecog"/>.
## </Description>
## </ManSection>
## <#/GAPDoc>
DeclareGlobalFunction( "RecogniseClassical" );

## <#GAPDoc Label="DisplayRecog">
## <ManSection>
## <Func Name="DisplayRecog" Arg="r"/>
## <Returns>nothing</Returns>
## <Description>
## Pretty-print selected information from the record returned by
## <Ref Func="RecogniseClassical"/>. This is mainly intended as a debugging
## helper for inspecting the internal state accumulated by the recognition
## procedure.
## </Description>
## </ManSection>
## <#/GAPDoc>
DeclareGlobalFunction( "DisplayRecog" );
