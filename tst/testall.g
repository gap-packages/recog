LoadPackage("recog");

# Reset RNG state here; normally, START_TEST would do that for us in
# each .tst file, but we deliberately do not use it so that we can run a
# given .tst file again and again with many different RNG states,
# precisely so that we can catch issues that only appear with some RNG
# states, but not with others.
FlushCaches(  );
Reset(GlobalRandomSource, 1);
Reset( GlobalMersenneTwister, 1 );

TestDirectory(DirectoriesPackageLibrary("recog", "tst/working"), rec(exitGAP := true));
FORCE_QUIT_GAP(1);
