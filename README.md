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

> [!IMPORTANT]
> Note that `--packagedirs` was introduced in GAP 4.15. For older version please
> refer to [Chapter 76 of the GAP reference manual](https://docs.gap-system.org/doc/ref/chap76.html)
> for alternative solutions.

> [!TIP]
> You can add this option to your GAP startup script. More information about
> this can be found in [Chapter 3 of the GAP reference manual](https://docs.gap-system.org/doc/ref/chap3.html).

## Loading

You can load recog via

    LoadPackage( "recog" );

## Documentation

The [recog documentation](https://gap-packages.github.io/recog/doc/chap0_mj.html)
describes how to use recog, how it works and how to extend it.

Recompiling the documentation locally is possible by the command `gap makedoc.g`
in the `recog` directory.

## Dependencies

- [AtlasRep](https://www.gap-system.org/packages/#AtlasRep)
- [FactInt](https://www.gap-system.org/packages/#FactInt)
- [Forms](https://www.gap-system.org/packages/#Forms)
- [genss](https://www.gap-system.org/packages/#genss)
- [orb](https://www.gap-system.org/packages/#orb)

## Feedback and support

If you have any bug reports, feature requests, or suggestions, then please
tell us via the
[issue tracker on GitHub](https://github.com/gap-packages/recog/issues).

In addition, the recog package has a mailing list, at
<recog@gap-system.org>, which can be used for holding discussions,
sharing information, and asking questions about the package. You can find
more information, and register to receive the mail sent to this list, at
<https://mail.gap-system.org/mailman/listinfo/recog>.
