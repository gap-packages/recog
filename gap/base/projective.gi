#############################################################################
##
##  projective.gi      recog package
##                                                        Max Neunhoeffer
##                                                            Ákos Seress
##
##  Copyright 2006-2008 by the authors.
##  This file is free software, see license information at the end.
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
    s := b[1,p] / a[1,p];
    for i in [1..Length(a)] do
        if s*a[i] <> b[i] then return false; fi;
    od;
    return true;
  end );

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

