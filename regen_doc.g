# Regenerate parts of the recog documentation from its source code

# we need the precise version of GAP in this directory; if recog is not
# yet loaded, that's no problem; otherwise, we need to work a bit to
# verify that this is the case, and otherwise exit with an error
if not IsBound(GAPInfo.PackagesLoaded.recog) then
    SetPackagePath("recog", "./");
    LoadPackage("recog");
else
    loadedPath := GAPInfo.PackagesLoaded.recog[1];
    # ask bash whether that path corresponds to the current directory
    res := Process( DirectoryCurrent(), "/bin/test",
                    InputTextNone(), OutputTextNone(),
                    [ GAPInfo.PackagesLoaded.recog[1], "-ef", "." ] );
    if res <> 0 then
        Error("A different version of recog was already loaded; please start GAP with the -A option!\n");
    fi;
fi;

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
        AppendTo(xmlfile, "<Item><C>", meth.stamp, "</C></Item>\n");
        AppendTo(xmlfile, "<Item>", meth.comment, "</Item>\n");
        AppendTo(xmlfile, "<Item><Ref Subsect=\"", meth.stamp, "\"/></Item>\n");
        AppendTo(xmlfile, "</Row>\n");
        AppendTo(xmlfile, "<HorLine/>\n");
    od;

    AppendTo(xmlfile, "</Table>\n");

    CloseStream(xmlfile);

end;

GenerateMethodsListXML := function(shortname, desc, db)
local xmlfile, meth;

    xmlfile := Concatenation("doc/_methods_", shortname, "_list.xml");
    xmlfile := OutputTextFile(xmlfile, false);
    SetPrintFormattingStatus(xmlfile, false);

    for meth in Set(RecNames(db)) do
        AppendTo(xmlfile, "<Subsection Label=\"", meth, "\">\n");
        AppendTo(xmlfile, "<Heading><C>", meth, "</C></Heading>\n");
        AppendTo(xmlfile, "<#Include Label=\"", meth, "\">\n");
        AppendTo(xmlfile, "</Subsection>\n");
   od;

    CloseStream(xmlfile);

end;

GenerateMethodsTableXML("matrix", "Matrix", FindHomDbMatrix);
GenerateMethodsTableXML("perm", "Permutation", FindHomDbPerm);
GenerateMethodsTableXML("proj", "Projective", FindHomDbProjective);

GenerateMethodsListXML("generic", "Generic", FindHomMethodsGeneric);
GenerateMethodsListXML("matrix", "Matrix", FindHomMethodsMatrix);
GenerateMethodsListXML("perm", "Permutation", FindHomMethodsPerm);
GenerateMethodsListXML("proj", "Projective", FindHomMethodsProjective);
