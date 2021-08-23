LoadPackage("recog");
RECOG_TEST_SUITE := "slow";
TestDirectory(
    Concatenation(DirectoriesPackageLibrary("recog", "tst/working/slow"),
                  DirectoriesPackageLibrary("recog", "tst/working/combined")),
    rec(exitGAP := true)
);
FORCE_QUIT_GAP(1);
