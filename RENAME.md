
This file gives further details on `rename.g` and it's associated files.

## DESCRIPTION

The `rename.g` file renames functions of the recog package and generates
a table of renamed functions for the documentation.
The `renamings_to_execute.csv` file specifies how to rename.
The `renamings_history.csv` file stores the history of renamings
and is used for the generation of the renaming table in the documentation.

## INSTRUCTIONS

Run the `rename.g` file with GAP from within the package directory.
There are two possible applications for running the file.

## APPLICATIONS

The first one adresses the developers of the recog package.
They can use this file to rename all occurences of a name `X`
in all .g, .gd, .gi, .tst, and .xml files to a name `Y`.
Below an example of this application is included.

The second one adresses people who use the recog package as a dependency.
They can apply the name changes that were executed inside the recog package to their own projects.

## DETAILS

The renamings_to_execute.csv and renamings_history.csv file have the following form:
* First column `OLD NAME` contains the old name.
* Second column `NEW NAME` contains the new name that is used now.
* Third column `TYPE` contains the type used for GAPDoc references, e.g. `Func` or `Attr`.

First let us discuss the case where the `renamings_to_execute.csv` file is not empty.
The other case can be explained afterwards.

First the `rename.g` file checks if the `renamings_to_execute.csv` file is syntactically correct.
Then further sanity checks are done and on failure Errors/Warnings are printed.
After successful checks all matches on word boundaries of the old name get
replaced with the new name. The replacements are executed in all files with
extensions .g, .gd, .gi, .tst, and .xml found in the directory tree rooted at '.'
whereas all files in the .git folder are ignored.
Afterwards the rows from the `renamings_to_execute.csv` file are added to
the `renamings_history.csv` file. Then the renaming table for the
documentation is generated from the `renamings_history.csv` file whereby
renamings of the form `X_1 -> X_2 -> ... -> X_n` are printed
in the documentation as `X_1 -> X_n`. Then the documentation of the recog package is regenerated.

Now let us discuss the case where the `renamings_to_execute.csv` file is empty.
Then the `rename.g` file attempts to execute the renamings in the order specified
by the `renamings_history.csv` file. This is useful if you are developing code that is not yet integrated into the `recog` package, already performed some renamings and need to catch up with the latest ones.
The replacements are executed as described in the first case.

## EXAMPLE

This example covers the use case for developers of the recog package.

Create the `renamings_to_execute.csv` file, so it looks like this:

    OLD NAME,NEW NAME,TYPE
    FindHomDbPerm,MoreDescriptiveNewName,Attr

Inside the package directory do:

    gap rename.g

Now the renamings that were stored inside the `renamings_to_execute.csv` file have been executed.
Thus `FindHomDbPerm` got replaced by `MoreDescriptiveNewName`.

It is recommended to run `gap tst/testquick.g` or `gap tst/testall.g` and ensure everything is still working:

    gap tst/testall.g

On failure you can always roll back to the last commit, i.e. the version before
applying the renamings. For example one could type in the command `git reset --hard`.

On success add and commit the changed files but make sure not to add the `renamings_to_execute.csv`:

    git add *
    git reset renamings_to_execute.csv
    git commit