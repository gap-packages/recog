#############################################################################
##
##  methsel.gi            recogbase package
##                                                        Max Neunhoeffer
##                                                            Ákos Seress
##
##  Copyright 2005-2008 by the authors.
##  This file is free software, see license information at the end.
##
##  Our own method selection.
##
#############################################################################

#
# A method is described by a record with the following components:
#  method     : the function itself
#  rank       : an integer rank
#  stamp      : a string describing the method uniquely
#  comment    : an optional comment to describe the method for humans
#  
# A database of methods is just a list of such records.
#
# Data for the method selection process is collected in another record
# with the following components:
#   falsemethods  : a record where each method that did not succeed
#                   left its stamp
#   failedmethods : a record where each method that failed temporarily
#                   left its stamp
#   successmethod : the stamp of the successful method in the end
#   tolerance     : last value of tolerance counter, see below
#   result        : either fail or true
#

# A constant:
InstallValue( NotApplicable, "NotApplicable" );

InstallGlobalFunction( "CallMethods", function(arg)
  # First argument is a record that describes the method selection process.
  # Second argument is a number, the tolerance limit.
  # All other arguments are handed through to the methods.

  local i,methargs,ms,result,tolerance,tolerancelimit,db;

  if Length(arg) < 2 then
      Error("CallMethods needs at least two arguments!");
  fi;
  db := arg[1];
  ms := rec(failedmethods := rec(), falsemethods := rec());
  tolerancelimit := arg[2];
  methargs := arg{[3..Length(arg)]};
  
  # Initialize record:
  tolerance := 0;    # reuse methods that failed that many times
  repeat   # a loop to try all over again with higher tolerance
      i := 1;
      while i <= Length(db) do
          if not(IsBound(ms.falsemethods.(db[i].stamp))) and
             (not(IsBound(ms.failedmethods.(db[i].stamp))) or
              ms.failedmethods.(db[i].stamp) <= tolerance) then

              # We try this one:
              Info(InfoMethSel,3,"Calling  rank ",db[i].rank,
                       " method \"", db[i].stamp,"\"...");
              result := CallFuncList(db[i].method,methargs);
              if result = false then
                  Info(InfoMethSel,3,"Finished rank ",db[i].rank,
                       " method \"", db[i].stamp,"\": false.");
                  ms.falsemethods.(db[i].stamp) := 1;
                  i := 1;    # start all over again
              elif result = fail then
                  Info(InfoMethSel,2,"Finished rank ",db[i].rank,
                       " method \"", db[i].stamp,"\": fail.");
                  if IsBound(ms.failedmethods.(db[i].stamp)) then
                      ms.failedmethods.(db[i].stamp) :=
                          ms.failedmethods.(db[i].stamp) + 1;
                  else
                      ms.failedmethods.(db[i].stamp) := 1;
                  fi;
                  i := 1;    # start all over again
              elif result = NotApplicable then
                  Info(InfoMethSel,3,"Finished rank ",db[i].rank,
                       " method \"", db[i].stamp,"\": not applicable.");
                  i := i + 1;   # just try the next one
              else    # otherwise we have a result
                  Info(InfoMethSel,2,"Finished rank ",db[i].rank,
                       " method \"", db[i].stamp,"\": success.");
                  ms.successmethod := db[i].stamp;
                  ms.result := result;
                  ms.tolerance := tolerance;
                  return ms;
              fi;
          else
              Info(InfoMethSel,4,"Skipping rank ",db[i].rank," method \"",
                   db[i].stamp,"\".");
              i := i + 1;
          fi;
      od;
      # Nothing worked, increase tolerance:
      Info(InfoMethSel,1,"Increasing tolerance to ",tolerance);
      tolerance := tolerance + 1;
  until tolerance > tolerancelimit;
  Info(InfoMethSel,1,"Giving up!");
  ms.result := fail;
  ms.tolerance := tolerance;
  return ms;
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

