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

#! TODO: document what is sensible
DeclareCategory("IsRecogMethod", IsObject);
BindGlobal("RecogMethodFamily", NewFamily("RecogMethodFamily", IsRecogMethod));
BindGlobal("RecogMethodType",
           NewType(RecogMethodFamily,
                   IsRecogMethod and IsAttributeStoringRep));

# Functions and attributes for IsRecogMethod objects
#! @Chapter methsel
#! @Section whataremethods
#! @Description
#! TODO: how to get this into the chapter with the GAPDoc label "methsel"?
#! TODO finish the draft below
#! method     : the function itself
#! rank       : an integer rank
#! stamp      : a string describing the method uniquely
#! comment    : an optional comment to describe the method for humans
DeclareGlobalFunction("RecogMethod");
DeclareGlobalFunction("CallRecogMethod");
DeclareAttribute("Stamp", IsRecogMethod);
DeclareAttribute("Comment", IsRecogMethod);
DeclareAttribute("ValidatesOrAlwaysValidInput", IsRecogMethod);
