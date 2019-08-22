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
  v -> Randomize(GlobalMersenneTwister, v));

InstallOtherMethod( Randomize, "for a mutable FFE vector and a random source",
  [ IsFFECollection and IsPlistRep and IsMutable, IsRandomSource ],
  { v, rs } -> Randomize(rs, v) );

InstallOtherMethod( Randomize, "for a random source and a mutable FFE vector",
  [ IsRandomSource, IsFFECollection and IsPlistRep and IsMutable ],
  function( rs, v )
    local f,i;
    f := DefaultField(v);
    for i in [1..Length(v)] do v[i] := Random(rs,f); od;
    return v;
  end );
