#############################################################################
##
##  methsel.gi            recog package
##                                                        Max Neunhoeffer
##                                                            Ákos Seress
##
##  Copyright 2005-2008 by the authors.
##  This file is free software, see license information at the end.
##
##  Our own method selection.
##
#############################################################################


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
#   inapplicableMethods  : a record where each method that is never applicable
#                   in this situation left its stamp
#   failedMethods : a record where each method that failed temporarily
#                   left its stamp
#   successMethod : the stamp of the successful method in the end
#   tolerance     : last value of tolerance counter, see below
#   result        : either fail or true
#

InstallGlobalFunction( "CallMethods", function(arg)
    # First argument is a method database, i.e. list of records
    #   describing recognition methods.
    # Second argument is a number, the tolerance limit.
    # All other arguments are handed through to the methods.

    local i, methargs, ms, result, tolerance, tolerancelimit, db;

    if Length(arg) < 2 then
        Error("CallMethods needs at least two arguments");
    fi;
    db := arg[1];
    ms := rec(failedMethods := rec(), inapplicableMethods := rec());
    tolerancelimit := arg[2];
    methargs := arg{[3..Length(arg)]};

    # Initialize record:
    tolerance := 0;    # reuse methods that failed that many times
    repeat   # a loop to try all over again with higher tolerance
        i := 1;
        while i <= Length(db) do
            # skip methods which are known to be inapplicableMethods
            if IsBound(ms.inapplicableMethods.(db[i].stamp)) then
                Info(InfoMethSel, 4, "Skipping inapplicableMethods rank ", db[i].rank,
                     " method \"", db[i].stamp, "\".");
                i := i + 1;
                continue;
            fi;

            # skip methods which signalled a temporary failure at a higher tolerance level
            if IsBound(ms.failedMethods.(db[i].stamp)) and
                ms.failedMethods.(db[i].stamp) > tolerance then
                Info(InfoMethSel, 4, "Skipping rank ", db[i].rank,
                     " method \"", db[i].stamp, "\".");
                i := i + 1;
                continue;
            fi;

            # apply the method
            Info(InfoMethSel, 3, "Calling rank ", db[i].rank,
                     " method \"", db[i].stamp, "\"...");
            result := CallFuncList(db[i].method,methargs);

            # evaluate the result
            if result = NeverApplicable then
                Info(InfoMethSel, 3, "Finished rank ", db[i].rank,
                     " method \"", db[i].stamp, "\": NeverApplicable.");
                ms.inapplicableMethods.(db[i].stamp) := 1;
                # method turned out to be inapplicable, but it may have computed
                # and stored new information -> start all over again
                # TODO: instead of guessing, add a way for methods to signal
                # if they actually did update something
                i := 1;

            elif result = TemporaryFailure then
                Info(InfoMethSel, 2, "Finished rank ", db[i].rank,
                     " method \"", db[i].stamp, "\": TemporaryFailure.");
                if IsBound(ms.failedMethods.(db[i].stamp)) then
                    ms.failedMethods.(db[i].stamp) :=
                        ms.failedMethods.(db[i].stamp) + 1;
                else
                    ms.failedMethods.(db[i].stamp) := 1;
                fi;
                # method failed (for now), but it may have computed
                # and stored new information -> start all over again
                i := 1;

            elif result = NotEnoughInformation then
                Info(InfoMethSel, 3, "Finished rank ", db[i].rank,
                     " method \"", db[i].stamp, "\": not currently applicable.");
                i := i + 1;   # just try the next one

            elif result = Success then    # we have a result
                Info(InfoMethSel, 2, "Finished rank ", db[i].rank,
                     " method \"", db[i].stamp, "\": success.");
                ms.successMethod := db[i].stamp;
                ms.result := result;
                ms.tolerance := tolerance;
                return ms;

            else
                Error("Recognition method return invalid result: ", result);
            fi;
        od;
        # Nothing worked, increase tolerance:
        Info(InfoMethSel, 1, "Increasing tolerance to ",tolerance);
        tolerance := tolerance + 1;
    until tolerance > tolerancelimit;

    Info(InfoMethSel, 1, "Giving up!");
    ms.result := TemporaryFailure;
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
