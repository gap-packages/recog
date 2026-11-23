gap> START_TEST("gh-00037.tst");
gap> oldInfoLevel := InfoLevel(InfoRecog);;
gap> SetInfoLevel(InfoRecog, 0);

# Issue #37
#@if not IsBound(RECOG_TEST_SUITE) or RECOG_TEST_SUITE <> "quick"
gap> for i in [1..50] do
>     ri := RECOG.TestGroup(GL(9,5), false, Size(GL(9,5)));
> od;
gap> for i in [1..50] do
>     ri := RECOG.TestGroup(GL(8,27), false, Size(GL(8,27)));
> od;
#@fi

#
gap> SetInfoLevel(InfoRecog, oldInfoLevel);
gap> STOP_TEST("gh-00037.tst");
