This file explains the usage of `rename.sh` and it's associated files.

## Description

The `rename.sh` file executes the `rename.g` file and regenerates the gap
documentation.
The `rename.g` file renames functions of the recog package and generates
a table of renamed functions for the documentation.
The `renamings_to_execute.csv` file specifies how to rename.
The `renamings_history.csv` file stores the history of renamings and is used
for the generation of the renaming table `doc/renaming_table.xml` in the
documentation.

## Applications

The first application adresses the developers of the recog package.
They can use the `rename.sh` script with an non-empty `renamings_to_execute.csv`
file to rename all occurences of a name `X` in all .g, .gd, .gi, .tst, and .xml
files to a name `Y`.
In the next two sections an explanation and an example how to use the
`rename.sh` to achieve this is included.

The second application is not yet fully implemented and adresses people who want
to contribute code to the recog package or use it as a dependency.
They can use the `renamge.g` script with an empty `renamings_to_execute.csv`
file to apply the name changes from the `renamings_history.csv` to their own
projects.
This use case is not yet fully implemented and is discussed in the section
[Replaying the history](#replaying-the-history).


## Explanation

The renamings_to_execute.csv and renamings_history.csv file have the following form:
* First column `OLD NAME` contains the old name.
* Second column `NEW NAME` contains the new name that is used now.
* Third column `TYPE` contains the type used for GAPDoc references, e.g. `Func` or `Attr`.

First the `rename.g` file checks if the `renamings_to_execute.csv` file is syntactically correct.
Then further sanity checks are done and on failure errors or warnings are printed.
In case of errors the script is aborted.
If no errors occured, `sed` is used to replace all matches on word boundaries
of the old name with the new name via `s/\bOLD_NAME\b/NEW_NAME/g`.
The replacements are executed in all files with extensions .g, .gd, .gi, .tst,
and .xml found in the directory tree rooted at '.' whereas all files in the
.git folder are ignored.
Afterwards the rows from the `renamings_to_execute.csv` file are added to
the `renamings_history.csv` file. Then the renaming table
`doc/renaming_table.xml` for the documentation is generated from the
`renamings_history.csv` file whereby renamings of the form `X_1 -> X_2 -> ...
-> X_n` are printed in the documentation as `X_1 -> X_n`.
Then the documentation of the recog package is cleaned via `doc/clean` and
regenerated.

## Example

Create the `renamings_to_execute.csv` file, so it looks like this:

    OLD NAME,NEW NAME,TYPE
    FindHomDbPerm,MoreDescriptiveNewName,Attr

Inside the package directory do:

    ./rename.sh

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

## Replaying the history

Now we discuss the case where the `renamings_to_execute.csv` file is empty.
Note that this use case is not yet fully implemented.
The `rename.g` file attempts to execute the renamings in the order specified by
the `renamings_history.csv` file. This is useful if you are developing code
that is not yet integrated into the `recog` package, maybe already performed
some renamings and need to catch up with the latest ones.  The replacements are
executed as described in the first case.
