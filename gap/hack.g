#############################################################################
##
##  hacks.g           recogbase package
##                                                        Max Neunhoeffer
##                                                            Ákos Seress
##
##  Copyright 2005-2008 by the authors.
##  This file is free software, see license information at the end.
##
##  Some corrections to the library.
##
#############################################################################

# Here I collect some hacks that are necessary with the current GAP,
# they should be removed some day:

InstallOtherMethod( ExtractSubMatrix, "hack: for lists of compressed vectors",
  [ IsList, IsList, IsList ],
  function( m, poss1, poss2 )
    local i,n;
    n := [];
    for i in poss1 do
        Add(n,ShallowCopy(m[i]{poss2}));
    od;
    if IsFFE(m[1][1]) then
        ConvertToMatrixRep(n);
    fi;
    return n;
  end );

InstallMethod( PseudoRandom, "for a group object with generators, use func", 
  [ IsGroup and HasGeneratorsOfGroup ], 1,
  function( g )
    local l;
    if IsBound(g!.pseudorandomfunc) and Length(g!.pseudorandomfunc) > 0 then
        l := Length(g!.pseudorandomfunc);
        return CallFuncList(g!.pseudorandomfunc[l].func,
                            g!.pseudorandomfunc[l].args);
    fi;
    TryNextMethod();
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

