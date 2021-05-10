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
##  Our own method selection.
##
#############################################################################


# Add a method to a database with "AddMethod" and call a method from a
# database with "CallMethods".
#
InstallGlobalFunction("AddMethod", function(methodDb, method)
    local l, pos;
    if not IsSubsetSet(NamesOfComponents(method),
                       ["method", "rank", "stamp"]) then
        ErrorNoReturn("<method> must have components",
                      " method, rank, and stamp");
    fi;
    if not IsBound(method.comment) then
        method.comment := "";
    fi;
    l := Length(methodDb);
    pos := First([1 .. l], i -> methodDb[i].rank <= method.rank);
    if pos = fail then
        pos := l + 1;
    fi;
    Add(methodDb, method, pos);
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

InstallGlobalFunction( "CallMethods", function(db, tolerancelimit, methargs...)
    # First argument is a method database, i.e. list of records
    #   describing recognition methods.
    # Second argument is a number, the tolerance limit.
    # All other arguments are handed through to the methods.

    local i, ms, result, tolerance;

    ms := rec(failedMethods := rec(), inapplicableMethods := rec());

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

            # skip methods which signalled a temporary failure at least
            # (tolerance + 1) times.
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
                ErrorNoReturn("Recognition method return invalid result: ", result);
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
