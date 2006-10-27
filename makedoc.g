##
##  this creates the documentation, needs: GAPDoc package, latex, pdflatex,
##  mkindex, dvips, recogbase package
##  
##  Call this with GAP.
##

RequirePackage("GAPDoc");

MakeGAPDocDoc("doc", "recog", [], "recog");

GAPDocManualLab("recog");

quit;

