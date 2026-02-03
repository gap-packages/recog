# SL2 recognition.

This directory contains code written by Frank Lübeck for black recognition of SL2,
and also incomplete code for recognition of SL3.

Some notes on the code:
- The files `memory.gd` and `memory.gi` contain code that is nowadays in the
  GAP library, in the files of the same name there.

  However, they are left in for now because so far nobody has double checked
  this -- it could be that only *most* of the code went into the GAP library,
  and that some additional helpers are present here but not there.

  But ideally these files should be deleted here, or at least all parts of
  them that are already in GAP.
- The files `slptools.gd` and `slptools.gi` contain code for working with SLPs.
  Here, too, someone should check if any of this is already in the GAP library.
  If so, delete those parts. Anything that is left should perhaps be added
  to GAP at some point?
- The file `SL2.g` contains code for black box recognition of $SL(2,q)$ based
  on the paper TODO.
- The file `SL3.g` contains *incomplete* code for black box recognition of
  $SL(3,q)$ based on the paper TODO.


## More on the $SL(2,q)$ code

The main function is `HomMatBlackSL2`. It currently returns a GAP homomorphism
object. We probably will want a modified version where the final part construction
this homomorphism is replaced by code producing the required SLPs / SLP generators
expected by recog (as outlined in the description for writing leaf methods in the
recog manual).

TODO:
- explain which generators are used / expected
- integrate it into recog proper


Note that we also have *existing* blackbox $SL(n,q)$ code by Peter Brooksbank
in file `gap/matrix/slconstr.gi` which could also be used in the SL2 case, but
according to tests by Frank, his code seems to be faster


Also note: the code requires $q$ 'large enough' (TODO: lookup and document the bound).

For small $q$ we are currently using BSGS methods in recog. But we should consider
writing specialized code for these case (e.g. for the smallest cases the groups
are so tiny that we should be able to produce optimal SLPs and stuff).
