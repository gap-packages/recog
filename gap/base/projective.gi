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
##  Generic code for projective groups.
##
#############################################################################

InstallGlobalFunction( IsOneProjective,
  function(el)
    local s, n, i, j, zero;
    n := Length(el[1]);
    Assert(1, DimensionsMat(el) = [n,n]);
    s := el[1,1];
    if IsZero(s) then return false; fi;
    zero := Zero(s);
    for i in [1..n] do
        if el[i,i] <> s then return false; fi;
        for j in [1..n] do
            if i <> j and el[i,j] <> zero then return false; fi;
        od;
    od;
    return true;
  end );

InstallGlobalFunction( IsEqualProjective,
  function(a,b)
    local p,s,i;
    p := PositionNonZero(a[1]);
    s := b[1,p];
    if IsZero(s) then return false; fi;
    s := s / a[1,p];
    for i in [1..Length(a)] do
        if s*a[i] <> b[i] then return false; fi;
    od;
    return true;
  end );
