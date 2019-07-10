##  this creates the documentation, needs: GAPDoc and AutoDoc packages, pdflatex
##
##  Call this with GAP from within the package directory.
##

if fail = LoadPackage("AutoDoc", ">= 2019.07.03") then
    ErrorNoReturn("AutoDoc 2019.07.03 or newer is required");
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
            "gap/matrix",
            "gap/perm",
            "gap/projective",
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
