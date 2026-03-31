.PHONY: doc html check

GAP ?= gap
GAP_ARGS = -q --quitonbreak --packagedirs $(abspath ..)

doc:
	$(GAP) $(GAP_ARGS) makedoc.g -c 'QUIT;'

html:
	NOPDF=1 $(GAP) $(GAP_ARGS) makedoc.g -c 'QUIT;'

check:
	$(GAP) $(GAP_ARGS) tst/testall.g

check-quick:
	$(GAP) $(GAP_ARGS) tst/testquick.g

check-slow:
	$(GAP) $(GAP_ARGS) tst/testslow.g

check-veryslow:
	$(GAP) $(GAP_ARGS) tst/testveryslow.g
