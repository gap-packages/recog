#############################################################################
##
##  methsel.gd          recogbase package
##                                                        Max Neunhoeffer
##                                                            Ákos Seress
##
##  Copyright 2005-2008 by the authors.
##  This file is free software, see license information at the end.
##
##  Declaration stuff for our own method selection.
##
#############################################################################

# Our own method selection code:

DeclareInfoClass( "InfoMethSel" );
SetInfoLevel(InfoMethSel,1);
DeclareGlobalFunction( "AddMethod" );
DeclareGlobalVariable( "NotApplicable" );
DeclareGlobalFunction( "CallMethods" );

# The following method has to be here because recogbase already uses
# it in its reading of the implemenation phase. This is if recogbase
# is loaded explicitly.

# Add a method to a database with "AddMethod" and call a method from a
# database with "CallMethods".
#
InstallGlobalFunction( "AddMethod", function(arg)
  # First argument is the method database, second is the method itself,
  # third is the rank, fourth is the stamp. An optional 5th argument is
  # the comment.
  local comment,db,i,l,mr,p;
  if Length(arg) < 4 or Length(arg) > 5 then
      Error("Usage: AddMethod(database,method,rank,stamp [,comment] );");
  fi;
  db := arg[1];
  mr := rec(method := arg[2],rank := arg[3],stamp := arg[4]);
  if Length(arg) = 5 then
      mr.comment := arg[5];
  else
      mr.comment := "";
  fi;
  l := Length(db);
  p := First([1..l],i->db[i].rank <= mr.rank);
  if p = fail then
      Add(db,mr);
  else
      for i in [l,l-1..p] do
          db[i+1] := db[i];
      od;
      db[i] := mr;
  fi;
end);


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

