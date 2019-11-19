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

# Checks a column col as follows.
# The columns is from the renamings_to_execute.csv file.
# The function checks whether col contains any word twice or more times.
# If a duplicate is found the function returns true.
# This is a helper function of CheckRenamingTable.
CheckRenamingTableForDuplicates := function(col, colName, message)
local failedCheck, toTest, word, i;
    
    toTest := Filtered(DuplicateFreeList(col), x -> Number(col, y -> y = x) > 1);
    failedCheck := not IsEmpty(toTest);
    while not IsEmpty(toTest) do
        word := Remove(toTest);
        Print(message,"\n\tThe word \'",word,"\' is located \n");
        for i in [1..Length(col)] do
            if col[i] = word then
                Print("\tin line ",i+1," in column \'",colName,"\' in file \'","renamings_to_execute.csv","\'\n");
            fi;
        od;
    od;
    return failedCheck;
end;

# Checks a column col as follows.
# The column is from the renamings_to_execute.csv file.
# The parameter shouldExist is a boolean that determines the output of the function.
# If shouldExist is true and all words in col exist in the recog package,
# then the function returns false.
# If shouldExist is false and all words in col do not exist in the recog package,
# then the function returns false.
# This is a helper function of CheckRenamingTable.
CheckExistenceOfWord := function(col, colName, shouldExist, message)
local failedCheck, failureInt, pos, word, result, dir, grep, streamIn, streamOut;

    failedCheck := false;
    failureInt := 0;
    if shouldExist = true then
        failureInt := 1;
    fi;
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
CheckRenamingTable := function(csvToExecute)
local colOld, colNew, colType,
      foundWarning, foundError, failedCheck, toTest, message, typeList, wrongTypes, wrongType;

    if NamesOfComponents(csvToExecute[1]) <> ["OLD_NAME","NEW_NAME","TYPE"] then
       Print("ERROR : The renamings_to_execute.csv file must contain the headline \'","OLD NAME,NEW NAME,TYPE","\'\n");
       Print("Aborting.\n");
       return true;
    fi;

    colOld := List([1..Length(csvToExecute)], i -> csvToExecute[i].OLD_NAME);
    colNew := List([1..Length(csvToExecute)], i -> csvToExecute[i].NEW_NAME);
    colType := List([1..Length(csvToExecute)], i -> csvToExecute[i].TYPE);

    foundWarning := false;
    foundError := false;

    message := "ERROR : Attempt to rename a function twice.";
    failedCheck := CheckRenamingTableForDuplicates(colOld, "OLD NAME", message);
    foundError := foundError or failedCheck;

    message := "ERROR : Attempt to use a new name twice.";
    failedCheck := CheckRenamingTableForDuplicates(colNew, "NEW NAME", message);
    foundError := foundError or failedCheck;

    message := "ERROR : Attempt to rename to an existing function.";
    failedCheck := CheckExistenceOfWord(colNew, "NEW NAME", false, message);
    foundError := foundError or failedCheck;

    if foundError then
        Print("Detected Errors.\nAborting.\n");
        return true;
    fi;

    typeList := ["Func", "Constr", "Meth", "Filt", "Prop", "Attr", "Var", "Fam", "InfoClass"];
    wrongTypes := Filtered([1..Length(csvToExecute)], i -> not colType[i] in typeList);
    while not IsEmpty(wrongTypes) do
        wrongType := Remove(wrongTypes);
        Print("WARNING : Non-valid type for GAPDoc references.\n\tThe wrong type is \'",colType[wrongType],"\'\n\tin line ", wrongType+1," in column \'","TYPE","\' in file \'","renamings_to_execute.csv","\'\n");
        foundWarning := true;
    od;

    message := "WARNING : Attempt to rename a non-existent function.";
    failedCheck := CheckExistenceOfWord(colOld, "OLD NAME", true, message);
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
# The csv is the current renamings_history.csv.
SimplifyCSVForRenamingTable := function(csv)
local i, j, word;

    i := 1;
    while i <= Length(csv) do
        word := csv[i].NEW_NAME;
        j := i + 1;
        while j <= Length(csv) do
            if csv[j].OLD_NAME = word then
                if csv[i].TYPE <> csv[j].TYPE then
                    Print("WARNING : A type has changed in a renaming of the form 'X -> Y -> Z'.\n\tThe type has changed for the word 'Y' = \'",word,"\'\n");
                fi;
                csv[i] := rec(OLD_NAME := csv[i].OLD_NAME, NEW_NAME := csv[j].NEW_NAME, TYPE := csv[j].TYPE);
                word := csv[i].NEW_NAME;
                Remove(csv, j);
            else
                j := j + 1;
            fi;
        od;
        i := i + 1;
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
    AppendTo(xmlfile, "\t<Item> <E>","Old Name","</E> </Item>\n");
    AppendTo(xmlfile, "\t<Item> <E>","New Name","</E> </Item>\n");
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

    if Filename( [DirectoryCurrent()], "renamings_to_execute.csv" ) = fail then
        message := "The renamings_to_execute.csv does not exist.\nDo you want to rename functions as specified in renamings_history.csv instead? [true/false]\n";
        if GetInputFromUser(message) = true then
            RenameFiles(csvHistory);
        else
            Print("Aborting.\n");
        fi;
    else
        csvToExecute := ReadCSV("renamings_to_execute.csv");
        if CheckRenamingTable(csvToExecute) = false then
            RenameFiles(csvToExecute);
        
            PrintCSV("renamings_history.csv", Concatenation(csvHistory, csvToExecute), ["OLD_NAME", "NEW_NAME", "TYPE"]);

            GenerateRenamingTable();
            Read("makedoc.g");
        fi;
    fi;
end;

RunRenaming();
