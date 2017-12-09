#############################################################################
##
##  init.g                recog package
##                                                        Max Neunhoeffer
##                                                            Ákos Seress
##                                                                 et al.
##
##  Copyright 2005-2008 by the authors.
##  This file is free software, see license information at the end.
##
##  Reading the declaration part of the recog package.
##
#############################################################################

ReadPackage("recog","gap/base/hack.g");
ReadPackage("recog","gap/base/methsel.gd");
ReadPackage("recog","gap/base/recognition.gd");

# The following contain generic declarations for different types of groups:
ReadPackage("recog","gap/base/perm.gd");
ReadPackage("recog","gap/base/matrix.gd");
ReadPackage("recog","gap/base/projective.gd");
ReadPackage("recog","gap/base/blackbox.gd");


ReadPackage("recog","gap/matrix.gd");
ReadPackage("recog","gap/projective.gd");
ReadPackage("recog","gap/blackbox.gd");

ReadPackage("recog","gap/tensor.gd");
#ReadPackage("recog","gap/forms.gd");
ReadPackage("recog","gap/ppd.gd");
ReadPackage("recog","gap/classical.gd");
ReadPackage("recog","gap/almostsimple.gd");
ReadPackage("recog","gap/findnormal.gd");
ReadPackage("recog","gap/classicalnatural.gd");
ReadPackage("recog","gap/AnSnOnFDPM.gd");
