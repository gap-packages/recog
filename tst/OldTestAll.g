LoadPackage("recog");

# All systematic tests:
ReadPackage("recog","tst/ProjC6.g");
ReadPackage("recog","tst/MatC6.g");
ReadPackage("recog","tst/ProjTensor.g");
ReadPackage("recog","tst/MatC3.g");
ReadPackage("recog","tst/MatC3_2.g");
ReadPackage("recog","tst/MatHSmax5.g");
ReadPackage("recog","tst/ProjDet.g");
ReadPackage("recog","tst/ProjTensorInduced.g");
ReadPackage("recog","tst/MatSn.g");
ReadPackage("recog","tst/MatAn.g");
ReadPackage("recog","tst/MatFDPM.g");
ReadPackage("recog","tst/MatTensor.g");
ReadPackage("recog","tst/TestClassicalNatural.g");
# FIXME occasional errors forGL(17,3), GL(18,7), GL(20,5)
ReadPackage("recog","tst/Sporadics.g");

# The following files from tst/ are NOT loaded by this test:
# - OldTestAll.g  -> of course
# - testsporadicrecog.g -> seems to work initially, but is very slow,
#     probably because we resort to orbit methods instead of constructive recognition
# - products.g -> read by other files
