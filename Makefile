GAPPATH = ../..

default: doc

doc:
	(echo 'Read("makedoc.g");' | $(GAPPATH)/bin/gap.sh -A -q -b)

clean:
	(cd doc ; ./clean)

.PHONY: default doc clean
