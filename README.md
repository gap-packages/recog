[![Build Status](https://github.com/gap-packages/recog/workflows/CI/badge.svg)](https://github.com/gap-packages/recog/actions?query=workflow%3A%22CI%22)
[![Code Coverage](https://codecov.io/github/gap-packages/recog/coverage.svg?branch=master)](https://app.codecov.io/gh/gap-packages/recog)

# recog

A GAP package for group recognition

## Installation

To get the newest version of this GAP 4 package download the
archive file `recog-x.x.tar.gz` and unpack it using

    tar xvf recog-x.x.tar.gz

Do this in a directory called `pkg`, preferably (but not necessarily)
in the `pkg` subdirectory of your GAP 4 installation. It creates a
subdirectory called `recog`.

This is all which is needed if you installed the package in the standard
`pkg` subdirectory.

Note that the recog package needs the `AtlasRep`, `FactInt`, `Forms`,
`genss`, and `orb` packages to work.

If you installed the package in another `pkg` directory than the standard
`pkg` directory in your GAP 4 installation, then you have to add the path
to the directory containing your `pkg` directory to GAP's list of directories.
This can be done by starting GAP with the `-l` command line option
followed by the name of the directory and a semicolon. Then your directory
is prepended to the list of directories searched. Otherwise the package
is not found by GAP. Of course, you can add this option to your GAP
startup script.

Recompiling the documentation is possible by the command `gap makedoc.g`
in the recog directory. But this should not be necessary.

## Feedback and support

If you have any bug reports, feature requests, or suggestions, then please
tell us via the
[issue tracker on GitHub](https://github.com/gap-packages/recog/issues).

In addition, the recog package has a mailing list, at
<recog@gap-system.org>, which can be used for holding discussions,
sharing information, and asking questions about the package.  You can find
more information, and register to receive the mail sent to this list, at
<https://mail.gap-system.org/mailman/listinfo/recog>.
