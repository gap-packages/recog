#############################################################################
## 
## This file is part of recog, a package for the GAP computer algebra system
## which provides a collection of methods for the constructive recognition
## of groups.
## 
## This files's authors include Sergio Siccha, Friedrich Rober.
## Work on this file started in Summer School Matrix Group Recognition 2019.
## This is project 14 on
## https://lbfm-rwth.github.io/Summer-School-MGRP/projects/
## 
## Copyright of recog belongs to its developers whose names are too numerous
## to list here. Please refer to the COPYRIGHT file for details.
## 
## SPDX-License-Identifier: GPL-3.0-or-later
## 
## Details can be found in RENAME.md
##
#############################################################################

GetInputFromUser := function(message)
local input;

    input := InputFromUser(message);
    if input = false then
        return false;
    elif input = true then
        return true;
    else
        Print("Input is not valid.\n");
        return GetInputFromUser(message);
    fi;
end;

# Returns true on failed check. Helper method of CheckRenamingTable.
# Check fails if there exist duplicate entries in colA and colB.
# If isFirstInHistory is true, then colA is from the renamings_history.csv file,
# otherwise from the renamings_to_execute.csv file.
# colB is always from the renamins_to_execute.csv file.
CheckRenamingTableForDuplicates := function(colA, colB, colNameA, colNameB, isFirstInHistory, message)
local failedCheck, toTest, word, posA, posB, fileA, fileB;
    
    if colNameA = colNameB and isFirstInHistory = false then
        toTest := Filtered(DuplicateFreeList(colA), x -> Number(colA, y -> y = x) > 1);
    else
        toTest := Intersection(colA, colB);
    fi;
    failedCheck := not IsEmpty(toTest);
    while not IsEmpty(toTest) do
        word := Remove(toTest);
        if isFirstInHistory then
            posA := First([1..Length(colA)], i -> colA[i] = word);
            fileA := "renamings_history.csv";
            posB := First([1..Length(colB)], i -> colB[i] = word);
            fileB := "renamings_to_execute.csv";
        else
            posA := First([1..Length(colA)], i -> colA[i] = word);
            fileA := "renamings_to_execute.csv";
            if colNameA = colNameB then
                posB := First([1..Length(colB)] + posA, i -> colB[i] = word);
                fileB := "renamings_to_execute.csv";
            else
                posB := First([1..Length(colB)], i -> colB[i] = word);
                fileB := "renamings_to_execute.csv";
            fi;
        fi;

        Print(message,"\n\tThe word \'",word,"\' is located \n\tin line ",posA+1," in column \'",colNameA,"\' in file \'",fileA,"\' and\n\tin line ",posB+1," in column \'",colNameB,"\' in file \'",fileB,"\'\n");
    od;
    return failedCheck;
end;

# Returns true on failed check. Helper method of CheckRenamingTable.
# Check fails if grep returns failureInt on search of a word in col.
# failureInt is either 0 or 1.
CheckExistenceOfWord := function(col, colName, failureInt, message)
local failedCheck, pos, word, result, dir, grep, streamIn, streamOut;

    failedCheck := false;
    for pos in [1..Length(col)] do
        word := col[pos];
        dir := DirectoryCurrent();
        grep := Filename(DirectoriesSystemPrograms(),"grep");
        streamIn := InputTextNone();
        streamOut := OutputTextNone();
        result := Process(dir, grep, streamIn, streamOut, ["-r", "--exclude-dir=.git", "--include=*.gd", "--include=*.gi", "--include=*.g", JoinStringsWithSeparator(["\\b",word,"\\b"], "")]);
        CloseStream(streamIn);
        CloseStream(streamOut);
        # result = 0 if word is found.
        # result = 1 if word not found.
        if result = failureInt then
            failedCheck := true;
            Print(message, "\n\tThe word \'",word,"\' is located \n\tin line ",pos+1," in column \'",colName,"\' in file \'renamings_to_execute.csv\'\n");
        fi;
    od;
    return failedCheck;
end;

# Returns true on failed check.
CheckRenamingTable := function(csvHistory, csvToExecute)
local colOldInHistory, colNewInHistory, colOldInToExecute, colNewInToExecute, colTypeInToExecute,
      foundWarning, foundError, failedCheck, toTest, message, typeList, wrongTypes, wrongType;

    if NamesOfComponents(csvToExecute[1]) <> ["OLD_NAME","NEW_NAME","TYPE"] then
       Print("ERROR : The renamings_to_execute.csv file must contain the headline \'","OLD NAME,NEW NAME,TYPE","\'\n");
       Print("Aborting.\n");
       return true;
    fi;

    colOldInHistory := List([1..Length(csvHistory)], i -> csvHistory[i].OLD_NAME);
    colNewInHistory := List([1..Length(csvHistory)], i -> csvHistory[i].NEW_NAME);
    colOldInToExecute := List([1..Length(csvToExecute)], i -> csvToExecute[i].OLD_NAME);
    colNewInToExecute := List([1..Length(csvToExecute)], i -> csvToExecute[i].NEW_NAME);
    colTypeInToExecute := List([1..Length(csvToExecute)], i -> csvToExecute[i].TYPE);

    foundWarning := false;
    foundError := false;

    message := "ERROR : Attempt to rename a function twice.";
    failedCheck := CheckRenamingTableForDuplicates(colOldInToExecute, colOldInToExecute, "OLD NAME", "OLD NAME", false, message);
    foundError := foundError or failedCheck;

    message := "ERROR : Attempt to use a new name twice.";
    failedCheck := CheckRenamingTableForDuplicates(colNewInToExecute, colNewInToExecute, "NEW NAME", "NEW NAME", false, message);
    foundError := foundError or failedCheck;

    message := "ERROR : Attempt to rename to an existing function.";
    failedCheck := CheckExistenceOfWord(colNewInToExecute, "NEW NAME", 0, message);
    foundError := foundError or failedCheck;

    message := "ERROR : Attempt to rename a non-existent function.";
    failedCheck := CheckExistenceOfWord(colOldInToExecute, "OLD NAME", 1, message);
    foundError := foundError or failedCheck;

    if foundError then
        Print("Detected Errors.\nAborting.\n");
        return true;
    fi;

    typeList := ["Func", "Constr", "Meth", "Filt", "Prop", "Attr", "Var", "Fam", "InfoClass"];
    wrongTypes := Filtered([1..Length(csvToExecute)], i -> not colTypeInToExecute[i] in typeList);
    while not IsEmpty(wrongTypes) do
        wrongType := Remove(wrongTypes);
        Print("WARNING : Non-valid attribute for the Ref element in GAPDoc.\n\tThe wrong type is \'",colTypeInToExecute[wrongType],"\'\n\tin line ", wrongType+1," in column \'","TYPE","\' in file \'","renamings_to_execute.csv","\'\n");
        foundWarning := true;
    od;

    message := "WARNING : Attempt to use a new name that was once an old name of a function.";
    failedCheck := CheckRenamingTableForDuplicates(colOldInHistory, colNewInToExecute, "OLD NAME", "NEW NAME", true, message);
    foundError := foundError or failedCheck;

    message := "WARNING : Attempt to rename a function again. This is a renaming of the form X -> Y -> Z.";
    failedCheck := CheckRenamingTableForDuplicates(colNewInHistory, colOldInToExecute, "NEW NAME", "OLD NAME", true, message);
    foundWarning := foundWarning or failedCheck;
    failedCheck := CheckRenamingTableForDuplicates(colNewInToExecute, colOldInToExecute, "NEW NAME", "OLD NAME", false, message);
    foundWarning := foundWarning or failedCheck;

    if foundWarning then
        message := "Detected Warnings. Do you want to continue? [true/false]\n";
        if GetInputFromUser(message) = false then
            Print("Aborting.\n");
            return true;
        fi;
    fi;
    return false;
end;

RenameFiles := function(csv)
local stringOut, dir, find, streamIn, streamOut, files, file, i;

    stringOut := "";
    dir := DirectoryCurrent();
    find := Filename(DirectoriesSystemPrograms(),"find");
    streamIn := InputTextNone();
    streamOut := OutputTextString(stringOut, false);
    Process(dir, find, streamIn, streamOut, [".", "-path", "./.git/*", "-prune", "-o", "!", "-type", "d", "-regex", ".*.\\(xml\\|gd\\|gi\\|g\\|tst\\)", "-print"]);
    CloseStream(streamIn);
    CloseStream(streamOut);
    files := SplitString(stringOut, "\n");

    for file in files do
        for i in [1..Length(csv)] do
            Exec(JoinStringsWithSeparator(["sed -i \"s/\\b",csv[i].OLD_NAME,"\\b/",csv[i].NEW_NAME,"/g\" ",file], ""));
        od;
    od;
end;

# Simplifies renamings of the form X_1 -> X_2 -> ... -> X_n by replacing them with X_1 -> X_n.
# The csv file is considered to have duplicate-free columns 'OLD NAME' and 'NEW NAME'.
SimplifyCSVForRenamingTable := function(csv)
local colNew, colOld, word, posInNew, posInOld;

    colNew := List([1..Length(csv)], i -> csv[i].NEW_NAME);
    colOld := List([1..Length(csv)], i -> csv[i].OLD_NAME);
    for word in Intersection(colNew, colOld) do
        posInNew := First([1..Length(csv)], i -> csv[i].NEW_NAME = word);
        posInOld := First([1..Length(csv)], i -> csv[i].OLD_NAME = word);
        csv[posInNew] := rec(OLD_NAME := csv[posInNew].OLD_NAME, NEW_NAME := csv[posInOld].NEW_NAME, TYPE := csv[posInOld].TYPE);
        Remove(csv, posInOld);
    od;
end;

# Generates the renaming table for the documentation from the renamings_history.csv file.
GenerateRenamingTable := function()
local xmlfile, csv, i;

    xmlfile := "./doc/renaming_table.xml";
    PrintTo(xmlfile);

    AppendTo(xmlfile, "<Table Align=\"|l|l|\">\n");
    AppendTo(xmlfile, "<Caption> renaming of functions</Caption>\n");
    AppendTo(xmlfile, "<HorLine/>\n");

    AppendTo(xmlfile, "<Row>\n");
    AppendTo(xmlfile, "\t<Item> <E>","OLD NAME","</E> </Item>\n");
    AppendTo(xmlfile, "\t<Item> <E>","NEW NAME","</E> </Item>\n");
    AppendTo(xmlfile, "</Row>\n");
    AppendTo(xmlfile, "<HorLine/>\n");

    csv := ReadCSV("renamings_history.csv");
    SimplifyCSVForRenamingTable(csv);

    for i in [1..Length(csv)] do
        AppendTo(xmlfile, "<Row>\n");
        AppendTo(xmlfile, "\t<Item> ",csv[i].OLD_NAME," </Item>\n");
        AppendTo(xmlfile, "\t<Item> <Ref ",csv[i].TYPE,"=\"", csv[i].NEW_NAME, "\"/> </Item>\n");
        AppendTo(xmlfile, "</Row>\n");
        AppendTo(xmlfile, "<HorLine/>\n");
    od;

    AppendTo(xmlfile, "</Table>\n");
    AppendTo(xmlfile, "</Chapter>\n");
end;

RunRenaming := function()
local csvHistory, csvToExecute, message;

    csvHistory := ReadCSV("renamings_history.csv");
    csvToExecute := ReadCSV("renamings_to_execute.csv");

    if IsEmpty(csvToExecute) then
        message := "The renamings_to_execute.csv is empty.\nDo you want to rename functions as specified in renamings_history.csv instead? [true/false]\n";
        if GetInputFromUser(message) = true then
            RenameFiles(csvHistory);
        else
            Print("Aborting.\n");
        fi;
    elif CheckRenamingTable(csvHistory, csvToExecute) = false then
        RenameFiles(csvToExecute);
        
        PrintCSV("renamings_history.csv", Concatenation(csvHistory, csvToExecute), ["OLD_NAME", "NEW_NAME", "TYPE"]);
        PrintTo("renamings_to_execute.csv", "OLD NAME,NEW NAME,TYPE");

        GenerateRenamingTable();
        Read("makedoc.g");
    fi;
end;

RunRenaming();
