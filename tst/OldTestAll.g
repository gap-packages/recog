LoadPackage("recog");

# All systematic tests:
ReadPackage("recog","tst/MatC6.g"); # SLOW
ReadPackage("recog","tst/MatTensor.g"); # slow
# FIXME occasional errors for GL(17,3), GL(18,7), GL(20,5)
ReadPackage("recog","tst/Sporadics.g");

# The following files from tst/ are NOT loaded by this test:
# - OldTestAll.g  -> of course
# - testsporadicrecog.g -> seems to work initially, but is very slow,
#     probably because we resort to orbit methods instead of constructive recognition
# - products.g -> read by other files
