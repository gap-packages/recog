##
##  this creates the documentation, needs: GAPDoc package, latex, pdflatex,
##  makeindex, dvips
##  
##  Call this with GAP.
##

RequirePackage("GAPDoc");

MakeGAPDocDoc("doc", "recogbase", [], "recogbase");

GAPDocManualLab("recogbase");

quit;

