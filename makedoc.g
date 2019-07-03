##  this creates the documentation, needs: GAPDoc and AutoDoc packages, pdflatex
##
##  Call this with GAP from within the package directory.
##

if fail = LoadPackage("AutoDoc", ">= 2016.01.21") then
    Error("AutoDoc 2016.01.21 or newer is required");
fi;

Read("regen_doc.g");

AutoDoc(rec(
    autodoc := rec(
        scan_dirs := [
            "doc",
            "gap",
            "gap/almostsimple",
            "gap/base",
            "gap/generic",
            ],
    ),
    scaffold := rec(
        bib := "recog",
        includes := [
            "intro.xml",
            "install.xml",
            "recognition.xml",
            "methsel.xml",
            "afterrecog.xml",
            "methods.xml",
            "examples.xml",
            ],
        ),
));


