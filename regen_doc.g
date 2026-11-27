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
##  Regenerate parts of the recog documentation from its source code
##
#############################################################################

# We need the precise version of recog contained in the current directory; if
# recog is not yet loaded, that's no problem; otherwise, we need to work a bit
# to verify that this is the case, and otherwise exit with an error Reading
# the implementation part of the recog package.
if not IsBound(GAPInfo.PackagesLoaded.recog) then
    SetPackagePath("recog", "./");
    LoadPackage("recog");
else
    loadedPath := GAPInfo.PackagesLoaded.recog[1];
    # ask bash whether that path corresponds to the current directory
    testPath := DirectoriesSystemPrograms();
    testPath := Filename(testPath, "test");
    res := Process( DirectoryCurrent(), testPath,
                    InputTextNone(), OutputTextNone(),
                    [ GAPInfo.PackagesLoaded.recog[1], "-ef", "." ] );
    if res <> 0 then
        ErrorNoReturn("a different version of recog was already loaded or you ",
                      "started GAP in the wrong directory; try ",
                      "`gap -A regen_doc.g` or `gap -A makedoc.g`");
    fi;
fi;

PlaceDefiningMethod := function(methodsRecord, methodName)
    local method, dir, file, line;
    method := methodsRecord.(methodName);
    dir := Filename(DirectoriesPackageLibrary("recog", ""), "");
    file := method!.filename;
    line := method!.linenumber;
    if StartsWith(file, dir) then
        file := file{[Length(dir)+1..Length(file)]};
    fi;
    return JoinStringsWithSeparator([file, line], ":");
end;

DbsWhichUseMethod := function(methodsRecord, methodName)
    local result, method, methodDbs, types, db, i;
    result := [];
    method := methodsRecord.(methodName);
    methodDbs := [FindHomDbPerm, FindHomDbMatrix, FindHomDbProjective];
    types := ["permutation", "matrix", "projective"];
    for i in [1..Length(methodDbs)] do
        db := methodDbs[i];
        if ForAny(db, x -> Stamp(x.method) = Stamp(method)) then
            Add(result, types[i]);
        fi;
    od;
    return result;
end;

MethodsOutsideDatabases := function()
    local result, methodRecordsNames, collection, collectionName, methodName;
    result := [];
    methodRecordsNames := ["FindHomMethodsGeneric", "FindHomMethodsPerm",
                           "FindHomMethodsMatrix", "FindHomMethodsProjective"];
    for collectionName in methodRecordsNames do
        collection := ValueGlobal(collectionName);
        for methodName in RecNames(collection) do
            if IsEmpty(DbsWhichUseMethod(collection, methodName)) then
                Add(result, [methodName, collectionName]);
            fi;
        od;
    od;
    return result;
end;

# The .g and .gi files below the directory <dir>, recursively.
PackageCodeFiles := function(dir)
    local files, name, path;
    files := [];
    for name in Set(DirectoryContents(dir)) do
        if name in [".", ".."] then
            continue;
        fi;
        path := Concatenation(dir, "/", name);
        if IsDirectoryPath(path) then
            Append(files, PackageCodeFiles(path));
        elif EndsWith(name, ".gi") or EndsWith(name, ".g") then
            Add(files, path);
        fi;
    od;
    return files;
end;

# Map "FindHomMethodsX.Name" of each method outside the databases to the
# code that refers to it: the names of the last BindRecogMethod,
# InstallGlobalFunction or line-initial assignment above each reference
# in the files under gap/. Comment lines do not count.
MethodCallers := function()
    local targets, callers, dir, file, line, current, parts, pos, after, t;
    targets := List(MethodsOutsideDatabases(),
                    m -> Concatenation(m[2], ".", m[1]));
    callers := rec();
    for t in targets do
        callers.(t) := [];
    od;

    dir := Concatenation(Filename(DirectoriesPackageLibrary("recog", ""), ""),
                         "gap");
    for file in PackageCodeFiles(dir) do
        current := fail;
        for line in SplitString(StringFile(file), "\n") do
            pos := PositionProperty(line, c -> not c in " \t");
            if pos = fail or line[pos] = '#' then
                continue;
            fi;

            # track the enclosing top-level definition
            if StartsWith(line, "BindRecogMethod(") then
                parts := SplitString(line, "\"");
                current := Concatenation(parts[2], ".", parts[4]);
            elif StartsWith(line, "InstallGlobalFunction(") then
                current := Filtered(SplitString(line, "(,")[2],
                                    c -> not c in " \"");
            elif pos = 1 and PositionSublist(line, ":=") <> fail then
                # only an identifier on the left, not e.g. "rec(opt :="
                parts := NormalizedWhitespace(
                             line{[1 .. PositionSublist(line, ":=") - 1]});
                if ForAll(parts, c -> IsAlphaChar(c) or IsDigitChar(c)
                                      or c in "_.") then
                    current := parts;
                fi;
            fi;

            # whole-word references, so that Blocks does not match
            # BlocksModScalars
            for t in targets do
                pos := PositionSublist(line, t);
                while pos <> fail do
                    after := pos + Length(t);
                    if (after > Length(line) or
                        not (IsAlphaChar(line[after]) or
                             IsDigitChar(line[after]) or line[after] = '_'))
                       and current <> fail and current <> t
                       and not current in callers.(t) then
                        Add(callers.(t), current);
                    fi;
                    pos := PositionSublist(line, t, pos);
                od;
            od;
        od;
    od;
    return callers;
end;

methodCallers := MethodCallers();

# The stamp of a caller that is a recognition method, else its full name.
CallerName := function(caller)
    local parts;
    parts := SplitString(caller, ".");
    if Length(parts) = 2 and StartsWith(parts[1], "FindHomMethods") then
        return parts[2];
    fi;
    return caller;
end;

# A caller as GAPDoc XML: a link for a recognition method, code otherwise.
# Not for table cells: GAPDoc's text tables fail on Ref with Style="Text".
CallerXML := function(caller)
    if CallerName(caller) <> caller then
        return Concatenation("<Ref Subsect=\"", CallerName(caller),
                             "\" Style=\"Text\"/>");
    fi;
    return Concatenation("<C>", caller, "</C>");
end;

# "a", "a and b", "a, b, and c"
JoinWithAnd := function(words)
    local n;
    n := Length(words);
    if n <= 2 then
        return JoinStringsWithSeparator(words, " and ");
    fi;
    return Concatenation(JoinStringsWithSeparator(words{[1 .. n - 1]}, ", "),
                         ", and ", words[n]);
end;

GenerateMethodsOutsideDatabasesTableXML := function()
    local xmlfile, m, callers;

    xmlfile := OutputTextFile("doc/_methods_unused_table.xml", false);
    SetPrintFormattingStatus(xmlfile, false);

    PrintTo(xmlfile, "<Table Align=\"|l|l|l|l|\">\n");
    AppendTo(xmlfile, "<Caption>Find homomorphism methods outside the ",
             "method databases</Caption>\n");
    AppendTo(xmlfile, "<HorLine/>\n");

    for m in MethodsOutsideDatabases() do
        callers := methodCallers.(Concatenation(m[2], ".", m[1]));
        AppendTo(xmlfile, "<Row>\n");
        AppendTo(xmlfile, "<Item><C>", m[1], "</C></Item>\n");
        AppendTo(xmlfile, "<Item>", Comment(ValueGlobal(m[2]).(m[1])), "</Item>\n");
        if IsEmpty(callers) then
            AppendTo(xmlfile, "<Item>none</Item>\n");
        else
            AppendTo(xmlfile, "<Item>",
                     JoinStringsWithSeparator(List(callers,
                         c -> Concatenation("<C>", CallerName(c), "</C>")), ", "),
                     "</Item>\n");
        fi;
        AppendTo(xmlfile, "<Item><Ref Subsect=\"", m[1], "\"/></Item>\n");
        AppendTo(xmlfile, "</Row>\n");
        AppendTo(xmlfile, "<HorLine/>\n");
    od;

    AppendTo(xmlfile, "</Table>\n");

    CloseStream(xmlfile);

end;

GenerateMethodsTableXML := function(shortname, desc, db)
local xmlfile, meth;

    xmlfile := Concatenation("doc/_methods_", shortname, "_table.xml");
    xmlfile := OutputTextFile(xmlfile, false);
    SetPrintFormattingStatus(xmlfile, false);

    PrintTo(xmlfile, "<Table Align=\"|l|l|l|l|\">\n");
    AppendTo(xmlfile, "<Caption>", desc, " group find homomorphism methods</Caption>\n");
    AppendTo(xmlfile, "<HorLine/>\n");

    SortBy(db, x -> -x.rank);
    for meth in db do
        AppendTo(xmlfile, "<Row>\n");
        AppendTo(xmlfile, "<Item>", meth.rank, "</Item>\n");
        AppendTo(xmlfile, "<Item><C>", Stamp(meth.method), "</C></Item>\n");
        AppendTo(xmlfile, "<Item>", Comment(meth.method), "</Item>\n");
        AppendTo(xmlfile, "<Item><Ref Subsect=\"", Stamp(meth.method), "\"/></Item>\n");
        AppendTo(xmlfile, "</Row>\n");
        AppendTo(xmlfile, "<HorLine/>\n");
    od;

    AppendTo(xmlfile, "</Table>\n");

    CloseStream(xmlfile);

end;

GenerateMethodsListXML := function(shortname, recordName)
    local xmlfile, db, dbsWhichUseMethod, callers, meth;

    db := ValueGlobal(recordName);
    xmlfile := Concatenation("doc/_methods_", shortname, "_list.xml");
    xmlfile := OutputTextFile(xmlfile, false);
    SetPrintFormattingStatus(xmlfile, false);

    for meth in Set(RecNames(db)) do
        AppendTo(xmlfile, "<Subsection Label=\"", meth, "\">\n");
        AppendTo(xmlfile, "<Heading><C>", meth, "</C></Heading>\n");
        # Where is this method used?
        AppendTo(xmlfile, "This method is defined in <F>", PlaceDefiningMethod(db, meth), "</F>.");
        AppendTo(xmlfile, "<P/>\n");
        dbsWhichUseMethod := DbsWhichUseMethod(db, meth);
        if not IsEmpty(dbsWhichUseMethod) then
            AppendTo(xmlfile, "This method is used for recognizing ",
                     JoinWithAnd(dbsWhichUseMethod), " groups.");
        else
            callers := methodCallers.(Concatenation(recordName, ".", meth));
            if IsEmpty(callers) then
                AppendTo(xmlfile, "This method is not used: it is in no ",
                         "method database, and no other code refers to it.");
            else
                AppendTo(xmlfile, "This method is in no method database. ",
                         "It is called, directly or through a hint (see ",
                         "Section <Ref Sect=\"hintsystem\"/>), by ",
                         JoinWithAnd(List(callers, CallerXML)), ".");
            fi;
        fi;
        AppendTo(xmlfile, "<P/>\n");
        AppendTo(xmlfile, "<#Include Label=\"", meth, "\">\n");
        AppendTo(xmlfile, "</Subsection>\n");
   od;

    CloseStream(xmlfile);

end;

GenerateMethodsTableXML("matrix", "Matrix", FindHomDbMatrix);
GenerateMethodsTableXML("perm", "Permutation", FindHomDbPerm);
GenerateMethodsTableXML("proj", "Projective", FindHomDbProjective);

GenerateMethodsOutsideDatabasesTableXML();

GenerateMethodsListXML("generic", "FindHomMethodsGeneric");
GenerateMethodsListXML("matrix", "FindHomMethodsMatrix");
GenerateMethodsListXML("perm", "FindHomMethodsPerm");
GenerateMethodsListXML("proj", "FindHomMethodsProjective");
