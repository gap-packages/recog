LoadPackage("recog");
RECOG_TEST_SUITE := "veryslow";
TestDirectory(
    Concatenation(DirectoriesPackageLibrary("recog", "tst/working/veryslow"),
                  DirectoriesPackageLibrary("recog", "tst/working/combined")),
    rec(exitGAP := true)
);
FORCE_QUIT_GAP(1);
