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

# HACK so that we can still treat RecogMethod objects as records
RECOG.MethodComponentMap := rec(stamp := "Stamp",
                                method := "func",
                                comment := "Comment");
InstallMethod(\., [IsRecogMethod, IsObject],
function(x, nr)
    local name, map;
    name := NameRNam(nr);
    if IsBound\.(RECOG.MethodComponentMap, nr) then
        return x!.(RECOG.MethodComponentMap.(name));
    fi;
    return x!.(name);
end);

# HACK treat records as RecogMethod objects
InstallOtherMethod(Stamp, [IsRecord],
function(r)
    return r.stamp;
end);

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

InstallOtherMethod(Comment, [IsRecord],
function(r)
    return r.comment;
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

InstallGlobalFunction(RecogMethod,
function(stamp, comment, func)
    local r;
    r := rec(func := func);
    ObjectifyWithAttributes(r, RecogMethodType,
                            Stamp, stamp,
                            Comment, comment);
    return r;
end);

InstallGlobalFunction(CallRecogMethod,
function(m, args)
    # HACK to be compatible with records
    if IsRecord(m) then
        return CallFuncList(m.method, args);
    elif IsRecogMethod(m) then
        return CallFuncList(UnpackRecogMethod(m), args);
    else
        ErrorNoReturn("wrong type of <m>");
    fi;
end);
