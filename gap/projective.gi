#############################################################################
##
##  projective.gi      recogbase package
##                                                        Max Neunhoeffer
##                                                            Ákos Seress
##
##  Copyright 2006 Lehrstuhl D für Mathematik, RWTH Aachen
##
##  Generic code for projective groups.
##
#############################################################################

InstallGlobalFunction( IsOneProjective,
  function(el)
    local s;
    s := el[1][1];
    if IsZero(s) then return false; fi;
    s := s^-1;
    return IsOne( s*el );
  end );

InstallGlobalFunction( IsEqualProjective,
  function(a,b)
    local p,s,i;
    p := PositionNonZero(a[1]);
    s := b[1][p] / a[1][p];
    for i in [1..Length(a)] do
        if s*a[i] <> b[i] then return false; fi;
    od;
    return true;
  end );

