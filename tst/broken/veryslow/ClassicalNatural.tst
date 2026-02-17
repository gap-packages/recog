#
gap> ReadPackage("recog", "tst/utils.g");
true

#
gap> TestRecogGL(9,5);; # FIXME buggy, see issue #37
gap> TestRecogGL(2,8);; # FIXME: see issue #12
gap> TestRecogGL(2,16);; # FIXME: see issue #12
gap> TestRecogGL(8,27);; # FIXME: see issue #12

#
gap> TestRecogGL(10,3);; # FIXME
gap> TestRecogGL(18,3);; # FIXME
gap> TestRecogGL(3,27);; # FIXME
