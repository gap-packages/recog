#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
##
##  Reading the declaration part of the recog package.
##
#############################################################################

ReadPackage("recog","gap/base/hack.g");
ReadPackage("recog","gap/base/methods.gd");
ReadPackage("recog","gap/base/methsel.gd");
ReadPackage("recog","gap/base/recognition.gd");
ReadPackage("recog","gap/base/kernel.gd");

# The following contain generic declarations for different types of groups:
ReadPackage("recog","gap/base/projective.gd");

ReadPackage("recog","gap/matrix/ppd.gd");
ReadPackage("recog","gap/matrix/classical.gd");
ReadPackage("recog","gap/projective/almostsimple.gd");
ReadPackage("recog","gap/projective/findnormal.gd");
ReadPackage("recog","gap/projective/AnSnOnFDPM.gd");


# GAP 4.16.0 introduces PositionNonZeroInRow; add some compatibility shims
# so that we can use it in older GAP versions, too.
if not IsBound(PositionNonZeroInRow) then

DeclareOperation( "PositionNonZeroInRow", [ IsMatrixOrMatrixObj, IsPosInt ] );
DeclareOperation( "PositionNonZeroInRow", [ IsMatrixOrMatrixObj, IsPosInt, IsInt ] );

InstallMethod( PositionNonZeroInRow,
  "for a row list matrix and a row number",
  [ IsRowListMatrix, IsPosInt ],
  function( mat, row )
    return PositionNonZero( mat[row] );
  end );

InstallMethod( PositionNonZeroInRow,
  "for a row list matrix, a row number, and a start position",
  [ IsRowListMatrix, IsPosInt, IsInt ],
  function( mat, row, from )
    return PositionNonZero( mat[row], from );
  end );

InstallMethod( PositionNonZeroInRow,
  "for a matrix or matrix object and a row number",
  [ IsMatrixOrMatrixObj, IsPosInt ],
  function( mat, row )
    return PositionNonZeroInRow( mat, row, 0 );
  end );

InstallMethod( PositionNonZeroInRow,
  "for a matrix or matrix object, a row number, and a start position",
  [ IsMatrixOrMatrixObj, IsPosInt, IsInt ],
  function( mat, row, from )
    local col, ncols, zero;

    ncols := NrCols( mat );
    zero := ZeroOfBaseDomain( mat );
    for col in [ Maximum( 1, from + 1 ) .. ncols ] do
      if mat[row, col] <> zero then
        return col;
      fi;
    od;

    return ncols + 1;
  end );

# also use the improved generic IsDiagonalMatrix based on PositionNonZeroInRow
# for improved performance
InstallMethod( IsDiagonalMatrix,
    "for a matrix",
    [ IsMatrixOrMatrixObj ],
    function( mat )
    local i, ncols, p;
    ncols := NrCols( mat );
    for i  in [ 1 .. NrRows( mat ) ]  do
        p := PositionNonZeroInRow( mat, i );
        if p <= ncols and p <> i then
            return false;
        fi;
        if PositionNonZeroInRow( mat, i, i ) <= ncols then
            return false;
        fi;
    od;
    return true;
    end);

fi;
