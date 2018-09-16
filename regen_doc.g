# Regenerate parts of the recog documentation from its source code

SetPackagePath("recog", "./");
LoadPackage("recog");

GenerateMethodsXML := function(shortname, desc, db)
local xmlfile, meth;

    xmlfile := Concatenation("doc/methods_", shortname, "_table.xml");
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

GenerateMethodsXML("matrix", "Matrix", FindHomDbMatrix);
GenerateMethodsXML("perm", "Permutation", FindHomDbPerm);
GenerateMethodsXML("proj", "Projective", FindHomDbProjective);
