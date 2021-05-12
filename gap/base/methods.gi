#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This files's authors include Sergio Siccha.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
##
##  Implementation of recog methods
##
#############################################################################

# HACK make RecogMethod objects callable as if they were functions
InstallMethod(CallFuncList, [IsRecogMethod, IsList],
{f, args} -> CallFuncList(f!.func, args));

BindGlobal("UnpackRecogMethod",
function(m)
    if not IsRecogMethod(m) then
        ErrorNoReturn("<m> must be a RecogMethod, but is ", m);
    fi;
    return m!.func;
end);

InstallMethod(ViewString, [IsRecogMethod],
function(m)
    local s;
    s := "<RecogMethod \"";
    Append(s, Stamp(m));
    Append(s, "\": ");
    Append(s, ViewString(UnpackRecogMethod(m)));
    Append(s, ">");
    return s;
end);

InstallMethod(PrintObj, [IsRecogMethod],
function(m)
    Print("RecogMethod(\"", Stamp(m), "\",\n");
    Print("\"", Comment(m), "\",\n");
    Print(UnpackRecogMethod(m));
    Print(");");
end);

InstallGlobalFunction(RecogMethod,
function(stamp, comment, arg...)
    local func, opt, r;
    if Length(arg) = 0 or Length(arg) > 2 then
        Error("usage: RecogMethod(stamp, comment[, opt], func)");
    fi;
    func := Remove(arg);
    if not IsFunction(func) then
        Error("<func> must be a function");
    fi;
    if Length(arg) = 1 then
        opt := arg[1];
        if not IsRecord(opt) then
            Error("<opt> must be a record");
        fi;
    else
        opt := rec();
    fi;

    r := rec(func := func);
    if IsBound(opt.validatesOrAlwaysValidInput) then
        r.validatesOrAlwaysValidInput := opt.validatesOrAlwaysValidInput;
    fi;
    ObjectifyWithAttributes(r, RecogMethodType,
                            Stamp, stamp,
                            Comment, comment);
    return r;
end);

InstallGlobalFunction(BindRecogMethod,
function(r, arg...)
    r.(arg[1]) := CallFuncList(RecogMethod, arg);
end);

InstallGlobalFunction(CallRecogMethod,
function(m, args)
    if not IsRecogMethod(m) then
        ErrorNoReturn("<m> must be a RecogMethod, but is ", m);
    fi;
    return CallFuncList(UnpackRecogMethod(m), args);
end);
