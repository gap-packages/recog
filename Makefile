.PHONY: run doc html clean check

GAP ?= gap
GAP_ARGS = -q --quitonbreak --packagedirs $(abspath .)

# run GAP and load the package
run:
	$(GAP) --packagedirs "$(abspath .)" -c 'LoadPackage("recog");'

doc:
	$(GAP) $(GAP_ARGS) makedoc.g -c 'QUIT;'

html:
	NOPDF=1 $(GAP) $(GAP_ARGS) makedoc.g -c 'QUIT;'

clean:
	cd doc && rm -f *.{aux,bbl,blg,brf,css,dvi,html,idx,ilg,ind,js,lab,log,out,pdf,pnr,ps,six,tex,toc,txt,xml.bib} _*.xml title.xml

check:
	$(GAP) $(GAP_ARGS) tst/testall.g

check-quick:
	$(GAP) $(GAP_ARGS) tst/testquick.g

check-slow:
	$(GAP) $(GAP_ARGS) tst/testslow.g

check-veryslow:
	$(GAP) $(GAP_ARGS) tst/testveryslow.g
