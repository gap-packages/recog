gap> START_TEST("ProjFDPMExpectedForm.tst");

# RECOG.ExpectedForm decides whether a row has the form b*(u_i - u_j). A row
# with all entries b except one, which is not 2b, does not, and the function
# returned nothing for it. 6_1.U4(3) in SU(6,2) leads to such a row.
gap> RECOG.ExpectedForm([1, 1, 1, 2] * Z(5)^0, 4, true);
[ Z(5)^0, [ 5, 6 ] ]
gap> RECOG.ExpectedForm([1, 1, 1, 3] * Z(5)^0, 4, true);
fail

# the other rows that are not of that form: two entries that are not
# negatives of each other, two entries other than b, too few entries
gap> RECOG.ExpectedForm([1, 2, 0, 0] * Z(5)^0, 4, true);
fail
gap> RECOG.ExpectedForm([1, 1, 2, 2] * Z(5)^0, 4, true);
fail
gap> RECOG.ExpectedForm([1, 1, 1, 0, 0, 0] * Z(5)^0, 6, true);
fail

#
gap> STOP_TEST("ProjFDPMExpectedForm.tst");
