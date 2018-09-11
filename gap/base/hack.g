#############################################################################
##
##  hacks.g           recog package
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
    if IsFFE(m[1,1]) then
        ConvertToMatrixRep(n);
    fi;
    return n;
  end );

InstallMethod( PseudoRandom, "for a group object with generators, use func",
  [ IsGroup and HasGeneratorsOfGroup ], 1,
  function( g )
    local l;
    # FIXME: get rid of this hackish override of PseudoRandom,
    # and define our own operation instead (say, RECOG_PseuoRandom)?!
    # Or at least change pseudorandomfunc to an attribute, so that
    # the filter of this method can be turned into something like
    #  IsGroup and HasPseudoRandomFunc
    if IsBound(g!.pseudorandomfunc) and Length(g!.pseudorandomfunc) > 0 then
        l := Length(g!.pseudorandomfunc);
        return CallFuncList(g!.pseudorandomfunc[l].func,
                            g!.pseudorandomfunc[l].args);
    fi;
    TryNextMethod();
  end );

# Randomize methods for non-compressed vectors, to support fields with more
# than 256 elements; needed by RECOG.RuleOutSmallProjOrder
InstallOtherMethod( Randomize, "for a mutable FFE vector",
  [ IsFFECollection and IsPlistRep and IsMutable ],
  v -> Randomize(v, GlobalMersenneTwister));

InstallOtherMethod( Randomize, "for a mutable FFE vector and a random source",
  [ IsFFECollection and IsPlistRep and IsMutable, IsRandomSource ],
  function( v, rs )
    local f,i;
    f := DefaultField(v);
    for i in [1..Length(v)] do v[i] := Random(rs,f); od;
    return v;
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

