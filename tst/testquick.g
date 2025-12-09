LoadPackage("recog");
RECOG_TEST_SUITE := "quick";
TestDirectory(
    Concatenation(DirectoriesPackageLibrary("recog", "tst/working/quick"),
                  DirectoriesPackageLibrary("recog", "tst/working/combined")),
    rec(exitGAP := true)
);
FORCE_QUIT_GAP(1);
