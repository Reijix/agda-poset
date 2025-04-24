.PHONY: all html clean push open

RTSOPTS = +RTS -M6G -A128M -RTS

IDM = hy84coky
HOST = cip1d1.cip.cs.fau.de

all: html

html: index.agda
	agda ${RTSOPTS} --html --html-dir=agda-poset index.agda -i.

agda: index.agda
	agda ${RTSOPTS} index.agda -i.

clean:
	find . -name '*.agdai' -exec rm \{\} \;

push: all
	scp -r agda-poset ${IDM}@${HOST}:.www/agda-stuff/

open:
	firefox agda-poset/index.html
