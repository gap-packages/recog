[![CI](https://github.com/gap-packages/recog/actions/workflows/CI.yml/badge.svg)](https://github.com/gap-packages/recog/actions/workflows/CI.yml)
[![Code Coverage](https://codecov.io/github/gap-packages/recog/coverage.svg?branch=master)](https://app.codecov.io/gh/gap-packages/recog)

# recog

A GAP package for group recognition

## Installation

To get the newest version of this GAP 4 package download the
archive file `recog-x.x.tar.gz` from
[here](https://github.com/gap-packages/recog/releases/latest).

### Standard installation
Unpack the archive using

    tar xvf recog-x.x.tar.gz

Do this in the `pkg` subdirectory of your GAP 4 installation. It creates a
subdirectory called `recog`.

### Custom installation

If you want to contribute to recog you might want to install it
into a custom directory. For example into the directory `~/packages`. Then you
can clone recog (or perhaps your personal fork of it) into `~/packages` via

    cd ~/packages
    git clone git@github.com:gap-packages/recog.git

To enable GAP to find recog you can start GAP via

    gap --packagedirs "~/packages;"

Of course, you can add this option to your GAP startup script.

## Loading

You can load recog via

    LoadPackage( "recog" );

## Documentation

The documentation can be found
[here](https://gap-packages.github.io/recog/doc/chap0_mj.html).
Recompiling the documentation locally is possible by the command `gap makedoc.g`
in the `recog` directory.

## Dependencies

- [AtlasRep](https://www.math.rwth-aachen.de/homes/Thomas.Breuer/atlasrep/)
- [FactInt](https://gap-packages.github.io/FactInt/)
- [Forms](https://gap-packages.github.io/forms)
- [genss](https://gap-packages.github.io/genss)
- [orb](https://gap-packages.github.io/orb)

## Feedback and support

If you have any bug reports, feature requests, or suggestions, then please
tell us via the
[issue tracker on GitHub](https://github.com/gap-packages/recog/issues).

In addition, the recog package has a mailing list, at
<recog@gap-system.org>, which can be used for holding discussions,
sharing information, and asking questions about the package. You can find
more information, and register to receive the mail sent to this list, at
<https://mail.gap-system.org/mailman/listinfo/recog>.
